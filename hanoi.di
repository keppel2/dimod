in 4 $pegs [3];
0 $move(in 2 $n,in 2 $A, in 2 $B, in 2 $C)
{
if($n>0)
{
$move($n-1,$A,$C,$B);
$pegs[$A]:$pegs[$A]-1;
$pegs[$C]:$pegs[$C]+1;
writeFill($pegs[]"\n");
$move($n-1,$B,$A,$C);
}
}
0 $main()
{
$pegs[0]:3;
writeFill("Start:"$pegs[]"\n");
$move(3,0,1,2);
writeFill("End:"$pegs[]"\n");
}
