// Author: Kevin Bealer
// Created: 2021

// This is a small puzzle solving program I wrote to solve Sokoban puzzles (and to practice my Rust
// language skills.) It uses an IDA* solver for the search part.
//
// The heuristic is two parts - first, I have a heuristic function that simply totals manhattan
// distances per block. This solves individual blocks well enough.
//
// Secondly, I have a 'composing' version that splits the problem into sub-problems, each including
// some of the blocks. Each subproblem is attacked recursively. The results of these searches are
// cached, resulting in a memoizing approach with something like a dynamic programming strategy.
//
// Next improvement should be to use intelligent clustering to make the composer more
// effective. This would improve recognition of 'mutually unmoveable blocks'.

use std::fmt;
use std::cmp;
use std::collections::HashMap;
use std::time::{Instant, Duration};
use std::fs::File;
use std::path::Path;
use std::io::prelude::*;

#[derive(Copy, Clone)]
enum Direction {
    North,
    East,
    South,
    West
}

impl fmt::Display for Direction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            Direction::North => "north",
            Direction::East  => "east",
            Direction::South => "south",
            Direction::West  => "west"
        };
        write!(f, "{}", name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Point {
    x : i32, y : i32
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.x, self.y)
    }
}

impl Point {
    fn move_dir(& self, d : Direction) -> Point {
        let (x, y) =
            match d {
                Direction::North => (self.x,     self.y - 1),
                Direction::East  => (self.x + 1, self.y),
                Direction::South => (self.x,     self.y + 1),
                Direction::West  => (self.x - 1, self.y)
            };

        Point { x, y }
    }
}

fn is_open_terrain(terrain : &Vec<Vec<u8>>, p : &Point) -> bool {
    if p.y < 0 || p.y >= (terrain.len() as i32) {
        return false;
    }

    if p.x < 0 || p.x >= (terrain[p.y as usize].len() as i32) {
        return false
    }

    match terrain[p.y as usize][p.x as usize] {
        b' ' => true,
        b'^' => true,
        _ => false
    }
}

fn vector_has_point(v : &Vec<Point>, point : &Point) -> bool {
    for p in v {
        if *p == *point {
            return true;
        }
    }
    false
}

struct SolverStats {
    solver_id    : String,
    expanded     : usize,
    generated    : usize,
    max_depth    : usize,
    timing       : bool,
    start_time   : Instant,
    elapsed      : Duration
}

enum Solution<'a> {
    Solved(SokoBoard<'a>),

    // Could not solve because of cost limit
    Limited,

    // No solution is possible (the tree was exhausted without hitting a limit)
    NoSolution
}

impl SolverStats {
    fn new(solver_id : String) -> SolverStats {
        let now = Instant::now();
        SolverStats {
            solver_id,
            expanded     : 0,
            generated    : 0,
            max_depth    : 0,
            timing       : false,
            start_time   : now,
            elapsed      : Duration::ZERO
        }
    }
    
    fn start_timer(&mut self) {
        // IMPROVE ME
        //
        // This works, but when calling into another solver, would be better to accumulate the time
        // so far for the current solver.
        //
        // if self.timing {
        //    panic!("Started timer but already running");
        // }
        self.start_time = Instant::now();
        self.timing = true;
    }

    fn end_timer(&mut self) {
        // See above
        //
        // if ! self.timing {
        //    panic!("Ended timer but not already running");
        // }
        let end_time = Instant::now();
        self.elapsed += end_time - self.start_time;
        self.timing = false;
    }

    fn count_expansion(&mut self, children : usize) {
        self.expanded += 1;
        self.generated += children;
    }

    fn adjust_max_depth(&mut self, depth : usize) {
        self.max_depth = cmp::max(self.max_depth, depth);
    }
}

impl fmt::Display for SolverStats {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        let (elapsed, running) =
            match self.timing {
                false => { (self.elapsed, "") },
                true => { (self.elapsed + (Instant::now() - self.start_time), " (running)") }
            };

        writeln!(f, "solver_id    : {}", self.solver_id)?;
        writeln!(f, "expanded     : {}", self.expanded)?;
        writeln!(f, "generated    : {}", self.generated)?;
        writeln!(f, "max_depth    : {}", self.max_depth)?;
        writeln!(f, "elapsed_time : {}{}", elapsed.as_secs_f64(), running)
    }
}

struct SolverStatsMap {
    stats : HashMap<String, SolverStats>
}

impl SolverStatsMap {
    fn new() -> SolverStatsMap {
        SolverStatsMap { stats : HashMap::new() }
    }

    fn modify(&mut self, solver_id : &String) -> &mut SolverStats {
        if ! self.stats.contains_key(solver_id) {
            self.stats.insert(solver_id.clone(), SolverStats::new(solver_id.clone()));
        }
        self.stats.get_mut(solver_id).unwrap()
    }
}

impl fmt::Display for SolverStatsMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        let mut keys = Vec::from_iter(self.stats.keys());
        keys.sort_unstable();

        for k in keys {
            let v = & self.stats[k];
            let id = & v.solver_id;
            writeln!(f, "--- Stats for solver ({}) ---", id)?;
            writeln!(f, "{}", v)?;
        }
        Ok(())
    }
}

struct SokoPuzzle {
    terrain  : Vec<Vec<u8>>,
    actor    : Point,
    blocks   : Vec<Point>,
    targets  : Vec<Point>
}

impl SokoPuzzle {
    fn new(lines : Vec<String>) -> SokoPuzzle {
        let mut terrain : Vec<Vec<u8>> = vec![];
        let mut actors  = vec![];
        let mut targets = vec![];
        let mut blocks  = vec![];

        let mut y = 0;
        let mut x;

        for line in lines {
            let mut tline = vec![];

            x = 0;

            for pos in line.bytes() {
                let mut ch = pos;

                match pos {
                    b'^' => { targets.push(Point { x, y }); }

                    b'@' => { ch = b' ';
                              actors.push(Point { x, y }); }

                    b'a' => { ch = b'^';
                              actors.push(Point { x, y });
                              targets.push(Point { x, y }); }

                    b'B' => { ch = b' ';
                              blocks.push(Point { x, y }); }

                    b'b' => { ch = b'^';
                              blocks.push(Point { x, y });
                              targets.push(Point { x, y }); }

                    _ => { }
                }
                tline.push(ch);
                x += 1;
            }

            terrain.push(tline);
            y += 1;
        }

        if actors.len() != 1 {
            panic!("Expected 1 actor on board, but found {}", actors.len());
        }
        blocks.sort_unstable();
        targets.sort_unstable();
        return SokoPuzzle { terrain, actor : actors.pop().unwrap(), blocks, targets };
    }

    fn set_point(pos         : &Point,
                 board       : &mut Vec<Vec<u8>>,
                 symbols_in  : &str,
                 symbols_out : &str) -> () {
        let x = pos.x as usize;
        let y = pos.y as usize;

        if symbols_in.len() != symbols_out.len() {
            panic!("symbol in/out tables have different lengths");
        }

        let ch = board[y][x];

        for item in symbols_in.as_bytes().iter().enumerate() {
            let (i,ch_in) : (usize, &u8) = item;
            if *ch_in == ch {
                board[y][x] = symbols_out.as_bytes()[i];
                return;
            }
        }

        panic!("Input symbol ({}) not found for translation map ({}) -> ({})",
               ch as char, symbols_in, symbols_out);
    }

    fn format_board(&self,
                    f      : &mut fmt::Formatter,
                    actor  : &Point,
                    blocks : &Vec<Point>) -> fmt::Result {
        let mut terrain_clone = self.terrain.clone();

        Self::set_point(actor, &mut terrain_clone, " ^", "@a");

        for block in blocks {
            Self::set_point(&block, &mut terrain_clone, " ^", "Bb");
        }

        for line in terrain_clone.iter() {
            writeln!(f, "{}", String::from_utf8(line.to_vec()).ok().unwrap())?;
        }
        fmt::Result::Ok(())
    }
}

#[derive(Clone)]
struct SokoBoard<'a> {
    puzzle : &'a SokoPuzzle,

    actor  : Point,
    blocks : Vec<Point>,

    moves  : i32,
    fcost  : i32,
    hcost  : i32,
    path   : String,
    digest : String
}

fn infinicost() -> i32 {
    1000000
}

fn compute_block_digest_string(blocks : &Vec<Point>) -> String {
    let mut digest = String::new();

    for b in blocks {
        let s = format!("{}", b);
        digest.push_str(& s);
    }
    digest
}

fn check_sorted(blocks : &Vec<Point>) {
    let mut sorted = blocks.clone();
    sorted.sort_unstable();

    if *blocks != sorted {
        let s1 = compute_block_digest_string(blocks);
        let s2 = compute_block_digest_string(& sorted);
        panic!("Computing digest for unsorted block vector {} != {}",
               s1, s2);
    }
}

fn compute_block_digest(blocks : &Vec<Point>) -> String {
    let mut digest = String::new();

    check_sorted(blocks);

    for b in blocks {
        let s = format!("{}", b);
        digest.push_str(& s);
    }
    digest
}

fn compute_digest(actor : &Point, blocks : &Vec<Point>) -> String {
    check_sorted(blocks);

    let block_digest = compute_block_digest(blocks);
    format!("{}-{}", actor, block_digest)
}

impl<'a> SokoBoard<'a> {
    fn new(puzzle     : &'a SokoPuzzle,
           costfn     : &mut impl Estimator,
           stats      : &mut SolverStatsMap,
           cost_cache : &mut CostCache) -> SokoBoard<'a> {

        Self::new_with_state( puzzle, puzzle.actor, puzzle.blocks.clone(), costfn, stats, cost_cache )
    }

    fn new_with_state(puzzle     : &'a SokoPuzzle,
                      actor      : Point,
                      mut blocks : Vec<Point>,
                      costfn     : &mut impl Estimator,
                      stats      : &mut SolverStatsMap,
                      cost_cache : &mut CostCache) -> SokoBoard<'a> {

        blocks.sort_unstable();
        let fcost  = costfn.compute_f(& puzzle, & actor, & blocks, stats, cost_cache);

        check_sorted(& blocks);

        let digest = compute_digest(& actor, & blocks);

        SokoBoard { puzzle, actor, blocks, moves : 0, fcost, hcost : fcost, path : String::new(), digest }
    }

    fn move_block(& self, pos : Point, d : Direction) -> Vec<Point> {
        let mut new_blocks : Vec<Point> =
            self.blocks.iter()
            .map(|b| if *b == pos { b.move_dir(d) } else { b.clone() })
            .collect();

        new_blocks.sort_unstable();
        new_blocks
    }

    fn move_direction(& self,
                      d          : Direction,
                      costfn     : &mut impl Estimator,
                      stats      : &mut SolverStatsMap,
                      cost_cache : &mut CostCache) -> Option<SokoBoard<'a>> {
        match self.can_move(d) {
            true => {
                let actor  = self.actor.move_dir(d);
                let mut blocks = self.move_block(actor, d);

                let moves = self.moves + 1;
                let fcost = costfn.compute_f(& self.puzzle, & actor, & blocks, stats, cost_cache);
                let hcost = moves + fcost;
                let mut path = self.path.clone();
                path.push(Self::direction_to_char(d));

                check_sorted(& blocks);

                let digest = compute_digest(& actor, & blocks);

                blocks.sort_unstable();

                Some( SokoBoard { puzzle : & self.puzzle,
                                  actor,
                                  blocks,
                                  moves,
                                  fcost,
                                  hcost,
                                  path,
                                  digest} )
            }
            false => None
        }
    }

    fn direction_to_char(d : Direction) -> char {
        match d {
            Direction::North => 'N',
            Direction::East  => 'E',
            Direction::South => 'S',
            Direction::West  => 'W'
        }
    }

    fn has_block(&self, p : &Point) -> bool {
        vector_has_point(& self.blocks, p)
    }

    fn can_move(&self, d : Direction) -> bool {
        let new_actor = self.actor.move_dir(d);

        if ! is_open_terrain(& self.puzzle.terrain, &new_actor) {
            return false;
        }

        if self.has_block(& new_actor) {
            let new_block = new_actor.move_dir(d);
            is_open_terrain(& self.puzzle.terrain, &new_block) && ! self.has_block(& new_block)
        } else {
            true
        }
    }

    fn get_children(&self,
                    costfn     : &mut impl Estimator,
                    stats      : &mut SolverStatsMap,
                    cost_cache : &mut CostCache) -> Vec<SokoBoard<'a>> {
        let mut rv = vec![];

        for d in [Direction::North,
                  Direction::East,
                  Direction::South,
                  Direction::West] {
            let child = self.move_direction(d, costfn, stats, cost_cache);

            match child {
                Some(node) => rv.push(node),
                None => { }
            }
        }

        return rv;
    }

    fn is_solved(&self) -> bool {
        self.fcost == 0
    }
}

impl<'a> fmt::Display for SokoBoard<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.puzzle.format_board(f, &self.actor, &self.blocks)?;
        writeln!(f, "Moves {} FCost {} HCost {} Digest {}", self.moves, self.fcost, self.hcost, self.digest)?;
        writeln!(f, "Solved ({}) Path ({})", self.is_solved(), self.path)
    }
}

// This expands the children of a node; if a solution is found, it just returns that
// Otherwise, it pushes the array of children into the vector.

fn expand_children<'a>(node       : &SokoBoard<'a>,
                       search     : &mut Vec<Vec<SokoBoard<'a>>>,
                       stats      : &mut SolverStatsMap,
                       solver_id  : &String,
                       costfn     : &mut impl Estimator,
                       cost_cache : &mut CostCache) -> Option<SokoBoard<'a>> {
    if node.is_solved() {
        println!("Already solved, just returning starting node");
        return Some(node.clone());
    }

    let mut children = node.get_children(costfn, stats, cost_cache);

    stats.modify(solver_id).count_expansion(children.len());

    // Iterate by index so I can move out the found element

    for i in 0..children.len() {
        if children[i].is_solved() {
            return Some(children.swap_remove(i));
        }
    }

    if ! children.is_empty() {
        search.push(children);
        stats.modify(solver_id).adjust_max_depth(search.len());
    }
    None
}

fn max_hcost_solver<'a>(start      : &SokoBoard<'a>,
                        max_hcost  : i32,
                        stats      : &mut SolverStatsMap,
                        solver_id  : &String,
                        costfn     : &mut impl Estimator,
                        cost_cache : &mut CostCache) -> Solution<'a> {

    let mut already_seen = HashMap::new();

    if max_hcost < 0 {
        return Solution::Limited
    }

    let mut search = vec![];

    already_seen.insert(start.digest.clone(), start.hcost);

    match expand_children(start, &mut search, stats, solver_id, costfn, cost_cache) {
        Some(soln) => { return Solution::Solved(soln); }
        None       => { }
    }

    let mut fail_result = Solution::NoSolution;

    while ! search.is_empty() {
        // unwrap - errors if there are no generations left

        let last_gen = search.last_mut().unwrap();
        let last_child = last_gen.pop();

        match last_child {
            // This indicates the generation was empty, so just erase it
            None => { search.pop(); }

            Some(child) => {
                if child.hcost > max_hcost {
                    fail_result = Solution::Limited;
                } else {
                    let seen_cost = already_seen.get(& child.digest);

                    let do_expand = match seen_cost {
                        None       => true,
                        Some(cost) => *cost > child.hcost
                    };

                    if do_expand {
                        already_seen.insert(child.digest.clone(), child.hcost);

                        match expand_children(& child, &mut search, stats, solver_id, costfn, cost_cache) {
                            Some(soln) => { return Solution::Solved(soln) }
                            None       => { }
                        }
                    }
                }
            }
        }
    }

    fail_result
}

fn read_board() -> Option<Vec<String>> {
    let path = Path::new("board.txt");
    let display = path.display();

    let mut file = match File::open(&path) {
        Err(why) => panic!("Failed to open board file ({}): {}", display, why),
        Ok(file) => file
    };

    let mut s = String::new();
    match file.read_to_string(&mut s) {
        Err(why) => panic!("Failed to read {}: {}", display, why),
        Ok(_) => { }
    }

    Some(s.lines().map(|s| s.to_string()).collect())
}

trait Estimator {
    fn compute_f(&mut self,
                 puzzle     : &SokoPuzzle,
                 actor      : &Point,
                 blocks     : &Vec<Point>,
                 stats      : &mut SolverStatsMap,
                 cost_cache : &mut CostCache) -> i32;
}

fn ida_star_solver<'a>(start      : &SokoBoard<'a>,
                       max_hcost  : i32,
                       costfn     : &mut impl Estimator,
                       stats      : &mut SolverStatsMap,
                       solver_id  : &String,
                       cost_cache : &mut CostCache) -> Solution<'a> {

    //let mut stats = SolverStats::new("ida*".to_string(),
    //                                 format!("max_hcost={}", max_hcost));

    for i in start.hcost..max_hcost {
        println!("\n*** Trying solution at hcost {} ***\n{}", i, start);

        let solution : Solution = max_hcost_solver(start, i, stats, &solver_id, costfn, cost_cache);

        match solution {
            Solution::Limited => {
                println!("\n\n *** Limit reached; no solution under hcost {}; stats:\n{}", i, stats);
            },

            Solution::NoSolution => {
                println!("\n\n *** No solution possible. Search tree exhausted before hcost {}; stats:\n{}", i, stats);
                return Solution::NoSolution;
            },

            Solution::Solved(solution) => {
                println!("Got a solution at hcost {}", i);
                return Solution::Solved(solution);
            }
        }
    }

    println!("Stopped search at maximum hcost {}", max_hcost);
    Solution::Limited
}

fn least_distance(object : & Point, goals : & Vec<Point>) -> i32 {
    let mut least = i32::MAX;

    for g in goals {
        let cost = manhattan(& object, & g);
        least = cmp::min(least, cost);
    }

    least
}

fn least_distance_unoccupied(object : & Point,
                             goals  : & Vec<Point>,
                             blocks : & Vec<Point>) -> i32 {
    let mut least = i32::MAX;

    // Compute least distance to an unoccupied goal. The rationale is that to use an occupied goal,
    // you would need to push the current occupant to another goal. But don't count the same block
    // as disqualifying the goal.

    for g in goals {
        if g == object {
            return 0;
        }
        if ! vector_has_point(blocks, g) {
            let cost = manhattan(& object, & g);
            least = cmp::min(least, cost);
        }
    }

    least
}

fn manhattan(a : &Point, b: &Point) -> i32 {
    return (a.x - b.x).abs() + (a.y - b.y).abs();
}

struct Manhattan { }

impl Manhattan {
    fn new() -> Manhattan {
        Manhattan { }
    }

    fn is_cornered(terrain : &Vec<Vec<u8>>, b : &Point) -> bool {
        let n = b.move_dir(Direction::North);
        let e = b.move_dir(Direction::East);
        let s = b.move_dir(Direction::South);
        let w = b.move_dir(Direction::West);

        // A block on a goal point is never considered cornered
        if is_open_terrain(terrain, &b) && terrain[b.y as usize][b.x as usize] == b'^' {
            return false;
        }

        // If the block is open on top and bottom or left and right, it is considered movable.
        if is_open_terrain(terrain, &n) && is_open_terrain(terrain, &s) {
            return false;
        }

        if is_open_terrain(terrain, &e) && is_open_terrain(terrain, &w) {
            return false;
        }

        return true;
    }
}

impl Estimator for Manhattan {
    fn compute_f(&mut self,
                 puzzle      : &SokoPuzzle,
                 actor       : &Point,
                 blocks      : &Vec<Point>,
                 _stats      : &mut SolverStatsMap,
                 _cost_cache : &mut CostCache) -> i32 {

        // Simple F cost - distance from the actor to the closest block (minus one) plus distance
        // from each block to the closest target

        // But actually - the cost is zero if all blocks are on targets, regardless of actor
        // position

        let mut total_cost = 0;

        // If any block is cornered, then the cost of the overall solution is infinite
        for b in blocks {
            if Self::is_cornered(& puzzle.terrain, b) {
                return infinicost();
            }
        }

        for b in blocks {
            total_cost += least_distance_unoccupied(& b, & puzzle.targets, & blocks);
        }

        if total_cost != 0 {
            total_cost += least_distance(& actor, & blocks) - 1;
        }

        total_cost
    }
}

struct CostCache {
    costs : HashMap<String, i32>
}

impl CostCache {
    fn new() -> CostCache {
        CostCache { costs : HashMap::new() }
    }
}

struct Composer { }

impl Composer {
    fn new() -> Composer {
        Composer { }
    }

    fn find_search_cost(&mut self,
                        puzzle     : &SokoPuzzle,
                        blocks     : &Vec<Point>,
                        stats      : &mut SolverStatsMap,
                        cost_cache : &mut CostCache) -> i32 {
        
        check_sorted(blocks);

        let digest = compute_block_digest(blocks);
        let cached = cost_cache.costs.get(& digest);

        match cached {
            None => {
                let computed = self.compute_cost(puzzle, blocks, stats, cost_cache);
                println!("--- Storing new cost {} for digest {} ---",
                         computed, digest);
                cost_cache.costs.insert(digest, computed);
                println!("--- Total stored solutions is now {} ---", cost_cache.costs.len());
                computed
            }
            Some(cost) => {
                *cost
            }
        }
    }

    fn compute_cost(&self,
                    puzzle     : &SokoPuzzle,
                    blocks     : &Vec<Point>,
                    stats      : &mut SolverStatsMap,
                    cost_cache : &mut CostCache) -> i32 {
        let mut actor_positions = vec![];

        for b in blocks {
            let mut positions = self.find_open_positions(puzzle, b);
            actor_positions.append(&mut positions);
        }

        actor_positions.sort_unstable();
        actor_positions.dedup();
        actor_positions.retain(|x| ! vector_has_point(blocks, x));

        let mut min_cost = infinicost();

        println!("--- Solving subpuzzle list for Composer strategy --- ");

        let mut i = 0;
        let position_count = actor_positions.len();

        for pos in actor_positions {
            i += 1;
            println!("--- Solving subpuzzle ({}/{}) for Composer strategy --- ",
                     i, position_count);

            let max_hcost = cmp::min(min_cost, 500);
            let subcost = self.compute_puzzle_cost(puzzle, pos, blocks, max_hcost, stats, cost_cache);

            if subcost == min_cost {
                println!(" *** Found identical cost solution (cost {} == {}) ***",
                        min_cost, subcost);
            } else if subcost < min_cost {
                println!(" *** Found new best solution (cost {} -> {}) ***",
                        min_cost, subcost);

                min_cost = subcost;
            }
        }

        println!("--- Subpuzzle list is done, min cost is {} ---", min_cost);

        min_cost
    }

    fn compute_puzzle_cost_with_fn(&self,
                                   puzzle     : &SokoPuzzle,
                                   actor      : Point,
                                   blocks     : &Vec<Point>,
                                   max_hcost  : i32,
                                   stats      : &mut SolverStatsMap,
                                   costfn     : &mut impl Estimator,
                                   cost_cache : &mut CostCache) -> i32 {
        let board = SokoBoard::new_with_state(puzzle, actor, blocks.clone(), costfn, stats, cost_cache);

        println!("--- Solving subpuzzle for Composer strategy (max cost {}) --- ",
                max_hcost);
        println!("{}", board);

        let sub_solver_id = "subset-puzzle-cost-fn".to_string();

        stats.modify(& sub_solver_id).start_timer();

        let result : Solution =
            ida_star_solver(& board,
                            max_hcost,
                            costfn,
                            stats,
                            &sub_solver_id,
                            cost_cache);

        stats.modify(& sub_solver_id).end_timer();

        let solution_hcost =
            match result {
                Solution::NoSolution       => { infinicost() },
                Solution::Limited          => { infinicost() },
                Solution::Solved(solution) => { solution.moves }
            };

        println!("--- Subpuzzle stats: ---\n{}", stats);

        solution_hcost
    }

    fn compute_puzzle_cost(&self,
                           puzzle     : &SokoPuzzle,
                           actor      : Point,
                           blocks     : &Vec<Point>,
                           max_hcost  : i32,
                           stats      : &mut SolverStatsMap,
                           cost_cache : &mut CostCache) -> i32 {
        if blocks.len() == 1 {
            println!("--- Using Manhattan Solver ---");
            let mut sub_cost_fn = Manhattan::new();
            self.compute_puzzle_cost_with_fn(puzzle, actor, blocks, max_hcost, stats, &mut sub_cost_fn, cost_cache)
        } else {
            println!("--- Using Composer Solver ---");
            let mut sub_cost_fn = Composer::new();
            self.compute_puzzle_cost_with_fn(puzzle, actor, blocks, max_hcost, stats, &mut sub_cost_fn, cost_cache)
        }
    }

    fn find_open_positions(&self, puzzle : &SokoPuzzle, block : &Point) -> Vec<Point> {
        let mut actor_positions = vec![];

        for d in [Direction::North,
                  Direction::East,
                  Direction::South,
                  Direction::West] {
            let pos = block.move_dir(d);

            if is_open_terrain(& puzzle.terrain, & pos) {
                actor_positions.push(pos);
            }
        }

        actor_positions
    }

    fn split_blocks(puzzle : &SokoPuzzle,
                    blocks : &Vec<Point>) -> Vec<Vec<Point>> {

        // Strategy : Sort by distance from the target, then split into two equal-sized groups
        
        let mut v : Vec<(i32, Point)> = blocks.iter().map(|b| (least_distance(& b, & puzzle.targets), *b)).collect();
        v.sort_unstable();

        let points : Vec<Point> = v.iter().map(|t| t.1).collect();
        let mut b1 = points[..points.len()/2].to_vec();
        let mut b2 = points[points.len()/2..].to_vec();
        b1.sort_unstable();
        b2.sort_unstable();
        vec![b1, b2]
    }
}

impl Estimator for Composer {
    fn compute_f(&mut self,
                 puzzle     : &SokoPuzzle,
                 actor      : &Point,
                 blocks     : &Vec<Point>,
                 stats      : &mut SolverStatsMap,
                 cost_cache : &mut CostCache) -> i32 {

        let mut total_cost = 0;

        if blocks.len() > 2 {
            let split = Self::split_blocks(puzzle, &blocks);

            for bv in &split {
                total_cost += self.find_search_cost(puzzle, &bv, stats, cost_cache);
            }
        } else {
            for b in blocks {
                let v = vec![*b];
                total_cost += self.find_search_cost(puzzle, & v, stats, cost_cache);
            }
        }

        if total_cost != 0 {
            total_cost += least_distance(& actor, & blocks) - 1;
        }

        total_cost
    }
}

fn main() {
    // Example of board syntax:
    //
    // ###########
    // #    ^    #
    // #    B @  #
    // #         #
    // ###########

    // Use this to 'set up' the board object quickly
    let mut mh_costfn = Manhattan { };

    let mut stats = SolverStatsMap::new();
    let solver_id = "main".to_string();

    stats.modify(& solver_id).start_timer();

    let mut cost_cache = CostCache::new();
    let mut costfn = Composer::new();
    let lines  = read_board().unwrap();
    let puzzle = SokoPuzzle::new(lines);
    let board  = SokoBoard::new(& puzzle, &mut mh_costfn, &mut stats, &mut cost_cache);

    println!("Starting board:\n");
    println!("{}", board);

    println!("Running Solver\n");

    let solution = ida_star_solver(& board, 500, &mut costfn, &mut stats, & solver_id, &mut cost_cache);

    stats.modify(& solver_id).end_timer();

    match solution {
        Solution::Solved(s)  => println!("Solution found:\n{}", s),
        Solution::Limited    => println!("No solution was found below the cost limit."),
        Solution::NoSolution => println!("No solution is possible (search space exhausted.)")
    }

    println!("Solver Stats:");
    println!("-------------");
    println!("{}", stats);
}
