% A Sudoku solver.  The basic idea is for each position,
% check that it is a digit with `digit`.  Then verify that the digit
% chosen doesn't violate any constraints (row, column, and cube).
% If no constraints were violated, proceed further.  If a constraint
% was violated, then backtrack to the last digit choice and move from
% there (the Prolog engine should handle this for you automatically).
% If we reach the end of the board with this scheme, it means that
% the whole thing is solved.

digit(1).
digit(2).
digit(3).
digit(4).
digit(5).
digit(6).
digit(7).
digit(8).
digit(9).

numBetween(Num, Lower, Upper) :-
        Num >= Lower,
        Num =< Upper.

% cubeBounds: (RowLow, RowHigh, ColLow, ColHigh, CubeNumber)
cubeBounds(0, 2, 0, 2, 0).
cubeBounds(0, 2, 3, 5, 1).
cubeBounds(0, 2, 6, 8, 2).
cubeBounds(3, 5, 0, 2, 3).
cubeBounds(3, 5, 3, 5, 4).
cubeBounds(3, 5, 6, 8, 5).
cubeBounds(6, 8, 0, 2, 6).
cubeBounds(6, 8, 3, 5, 7).
cubeBounds(6, 8, 6, 8, 8).

% Given a board and the index of a column of interest (0-indexed),
% returns the contents of the column as a list.
% columnAsList: (Board, ColumnNumber, AsRow)
columnAsList([], _, []).
columnAsList([Head|Tail], ColumnNum, [Item|Rest]) :-
        nth0(ColumnNum, Head, Item),
        columnAsList(Tail, ColumnNum, Rest).

% given which row and column we are in, gets which cube
% is relevant.  A helper ultimately for `getCube`.
% cubeNum: (RowNum, ColNum, WhichCube)
cubeNum(RowNum, ColNum, WhichCube) :-
        cubeBounds(RowLow, RowHigh, ColLow, ColHigh, WhichCube),
        numBetween(RowNum, RowLow, RowHigh),
        numBetween(ColNum, ColLow, ColHigh).

% Drops the first N elements from a list.  A helper ultimately
% for `getCube`.
% drop: (InputList, NumToDrop, ResultList)
drop([], _, []).
drop(List, 0, List).
drop([_|Tail], Num, Rest) :-
        Num > 0,
        NewNum is Num - 1,
        drop(Tail, NewNum, Rest).

% Takes the first N elements from a list.  A helper ultimately
% for `getCube`.
% take: (InputList, NumToTake, ResultList)
take([], _, []).
take(_, 0, []).
take([Head|Tail], Num, [Head|Rest]) :-
        Num > 0,
        NewNum is Num - 1,
        take(Tail, NewNum, Rest).

% Gets a sublist of a list in the same order, inclusive.
% A helper for `getCube`.
% sublist: (List, Start, End, NewList)
sublist(List, Start, End, NewList) :-
        drop(List, Start, TempList),
        NewEnd is End - Start + 1,
        take(TempList, NewEnd, NewList).

% Given a board and cube number, gets the corresponding cube as a list.
% Cubes are 3x3 portions, numbered from the top left to the bottom right,
% starting from 0.  For example, they would be numbered like so:
%
% 0  1  2
% 3  4  5
% 6  7  8
%
% getCube: (Board, ColumnIndex, ContentsOfCube)
getCube(Board, Number, AsList) :-
        cubeBounds(RowLow, RowHigh, ColLow, ColHigh, Number),
        sublist(Board, RowLow, RowHigh, [Row1, Row2, Row3]),
        sublist(Row1, ColLow, ColHigh, Row1Nums),
        sublist(Row2, ColLow, ColHigh, Row2Nums),
        sublist(Row3, ColLow, ColHigh, Row3Nums),
        append(Row1Nums, Row2Nums, TempRow),
        append(TempRow, Row3Nums, AsList).

% Given a board, solve it in-place.
% After calling `solve` on a board, the board should be fully
% instantiated with a satisfying Sudoku solution.


findNum(0, [X|_], X).    

findNum(Index, [_|Y], X):-
Index > 0,
NewIndex is Index - 1,
findNum(NewIndex, Y, X).  




solve(Board) :-

convertToList(Board, columns(Columns), cubes(Cubes)),
fillRows(Board, Board, Cubes, Columns, 0).
fillRows(_, _, _, _, 9).
fillColumns(_, _, _, 9, _, _, _).

noDuplicates(List) :-
        sort(List, Set),
        length(List, 9),
        length(Set, 9).


fillRows(Board, [Front|End], CubeNum, ColNum, RowNum) :-
	%Check if we are within the bounds
        RowNum >= 0,
        RowNum < 9,

        %Fill the columns associated with the current row
	fillColumns(Board, Front, Front, 0, ColNum, CubeNum, RowNum),
        noDuplicates(ColNum),
        noDuplicates(CubeNum),
        numBetween(RowNum, 0, 9),

        %Advance to the next row to set up the recursive call
	NextRow is RowNum + 1, 

        %Make recursive call
	fillRows(Board, End, CubeNum, ColNum, NextRow).




%Function that converts the columns and cubes of the board to lists.
convertToList(Board, columns([Column0, Column1, Column2, Column3, Column4, Column5, Column6, Column7, Column8]), cubes([Cube0, Cube1, Cube2, Cube3, Cube4, Cube5, Cube6, Cube7, Cube8])) :-

        %Convert columns to lists.
        columnAsList(Board, 0, Column0), 
        columnAsList(Board, 1, Column1), 
        columnAsList(Board, 2, Column2), 
        columnAsList(Board, 3, Column3), 
        columnAsList(Board, 4, Column4), 
        columnAsList(Board, 5, Column5), 
        columnAsList(Board, 6, Column6), 
        columnAsList(Board, 7, Column7), 
        columnAsList(Board, 8, Column8),

        %Convert cubes to lists.
        getCube(Board, 0, Cube0), 
        getCube(Board, 1, Cube1), 
        getCube(Board, 2, Cube2), 
        getCube(Board, 3, Cube3), 
        getCube(Board, 4, Cube4), 
        getCube(Board, 5, Cube5),
        getCube(Board, 6, Cube6), 
        getCube(Board, 7, Cube7), 
        getCube(Board, 8, Cube8).


fillColumns(Board, Head, [Front|End], ColNum, Entries, CubeNum, RowNum) :-
        %Check if we are within the bounds
        ColNum >= 0,
	ColNum < 9,

        %If current entry is empty, fill it with a valid number  
	fillEmpty(Board, Head, Front, RowNum, ColNum, CubeNum, Entries),
       
        noDuplicates(CubeNum),
        noDuplicates(Entries),
        numBetween(ColNum, 0, 9),

        %Advance to the next column to set up the recursive call 
	NextColumn is ColNum + 1, 

        %Make recursive call
	fillColumns(Board, Head, End, NextColumn, Entries, CubeNum, RowNum). 



fillEmpty(Board, List, Entry, RSolve, CSolve, CubeSolve, ColList) :-
	%If entry is non-empty, stop.
        not(var(Entry));

        %Else
	var(Entry),
        numBetween(RSolve, 0, 9),
        numBetween(CSolve, 0, 9),
	digit(Entry),
	findNum(CSolve, ColList, SolvedCol),
	cubeNum(RSolve, CSolve, CubeNum),
	findNum(CubeNum, CubeSolve, NewCube),

	%Check if all aspects of board are unique
        noDuplicates(SolvedCol),
	noDuplicates(NewCube),
	noDuplicates(List).

isValidNum(Num) :-
        Num > 0,
        Num =< 9.

range(X,K) :- X >= 0, X < K-1.


% Prints out the given board.
printBoard([]).
printBoard([Head|Tail]) :-
        write(Head), nl,
        printBoard(Tail).

test1(Board) :-
        Board = [[2, _, _, _, 8, 7, _, 5, _],
                 [_, _, _, _, 3, 4, 9, _, 2],
                 [_, _, 5, _, _, _, _, _, 8],
                 [_, 6, 4, 2, 1, _, _, 7, _],
                 [7, _, 2, _, 6, _, 1, _, 9],
                 [_, 8, _, _, 7, 3, 2, 4, _],
                 [8, _, _, _, _, _, 4, _, _],
                 [3, _, 9, 7, 4, _, _, _, _],
                 [_, 1, _, 8, 2, _, _, _, 5]],
        solve(Board),
        printBoard(Board).

test2(Board) :-
        Board = [[_, _, _, 7, 9, _, 8, _, _],
                 [_, _, _, _, _, 4, 3, _, 7],
                 [_, _, _, 3, _, _, _, 2, 9],
                 [7, _, _, _, 2, _, _, _, _],
                 [5, 1, _, _, _, _, _, 4, 8],
                 [_, _, _, _, 5, _, _, _, 1],
                 [1, 2, _, _, _, 8, _, _, _],
                 [6, _, 4, 1, _, _, _, _, _],
                 [_, _, 3, _, 6, 2, _, _, _]],
        solve(Board),
        printBoard(Board).
