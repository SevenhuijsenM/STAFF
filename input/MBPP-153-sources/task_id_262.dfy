method SplitArray(arr: array<int>, L: int) returns (firstPart: seq<int>, secondPart: seq<int>)
  requires 0 <= L <= arr.Length
  ensures |firstPart| == L
  ensures |secondPart| == arr.Length - L
  ensures firstPart + secondPart == arr[..]
{
  firstPart := arr[..L];
  secondPart := arr[L..];
}


method PrintSplitArray(firstPart: seq<int>, secondPart: seq<int>){
  print("[");
  print(firstPart);
  print(",");
  print(secondPart);
  print("]\n");

}
