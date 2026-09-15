- When you write a proof, start by writing a draft version in a temp
  file. Iterate there. When you're done, inspect your work, see if
  there are lemmas to extract. Clean up the proof. When that is done,
  move the proof into a non-temp file. Proofs should be written in a
  top down manner. State the main theorem, then introduce your lemmas
  and setup below the theorem using have statements and etc. A reader
  of the file should see the statement of the theorem before its proof
  details whenever possible.
- Feel free to use helpers from the library in Host. After
  you've written your proof and before moving it to a non-temp file,
  make a pass over existing proofs and see if any could reuse
  machinery you have developed. If they can, extract that into the
  library and feel empowered to modify existing proofs to use it.
- Be careful about preimptively extracting machinery into the
  library. Instead, whenever you finish a proof, review all the
  existing proofs to identify machinery that they reuse. This way the
  proof library grows in response to demand rather than speculative.
