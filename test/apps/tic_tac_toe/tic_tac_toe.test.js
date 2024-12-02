import { runMainCode, runMainCodeError } from "../../../bin/test/apps/apps_nf.js";
import { describe, it } from "node:test";

const no_winner_main = "public function main(): Bool { var bb = Board::initialBoard; bb = bb.setCell(0n, 0n, PlayerMark#x); bb = bb.setCell(1n, 1n, PlayerMark#o); return bb.checkAnyWinner() === none; }";
const x_winner_main = "public function main(): Bool { var bb = Board::initialBoard; bb = bb.setCell(0n, 0n, PlayerMark#x); bb = bb.setCell(1n, 1n, PlayerMark#o); bb = bb.setCell(0n, 1n, PlayerMark#x); bb = bb.setCell(1n, 0n, PlayerMark#o); bb = bb.setCell(0n, 2n, PlayerMark#x); let winner = bb.checkAnyWinner(); return winner === PlayerMark#x; }";

const oob_main = "public function main(): Bool { var bb = Board::initialBoard; bb = bb.setCell(0n, 4n, PlayerMark#x); return true; }";
const occupied_main = "public function main(): Bool { var bb = Board::initialBoard; bb = bb.setCell(0n, 0n, PlayerMark#x); bb = bb.setCell(0n, 0n, PlayerMark#o); return true; }";

describe ("TicTacToe", () => {
    it("should winner", function () {
        runMainCode("tic_tac_toe/tic_tac_toe.bsq", no_winner_main, [true, "Bool"]); 
        runMainCode("tic_tac_toe/tic_tac_toe.bsq", x_winner_main, [true, "Bool"]); 
    });

    it("should fail access", function () {
        runMainCodeError("tic_tac_toe/tic_tac_toe.bsq", oob_main, "Error -- i < this.size() @ list.bsq"); 
    });

    it("should fail occupied", function () {
        runMainCodeError("tic_tac_toe/tic_tac_toe.bsq", occupied_main, "Error -- this.isCellEmpty(r, c) @ test.bsq"); 
    });
});
