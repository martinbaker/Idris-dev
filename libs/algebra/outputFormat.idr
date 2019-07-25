||| outputs mathematical structures in more human readible way.
module outputForm

-- import public ???

%access public export

{-

-}

||| CharRectangle is a type synonym for a 2D array of characters.
||| This is intended to be used for output in a fixed-width font.
||| No need to have dimensions at the type level because the validity of
||| operations will not depend on width or height.
||| Functions will assume all rows are the same width, this must be enforced
||| by constructors.
CharRectangle : Type
CharRectangle = List (List Char)

||| constructor to create single line rectangle
charRectangle : String -> CharRectangle
charRectangle a = [unpack a]

||| constructor to create rectangle with an array of empty spaces.
paddedRectangle : Nat -> Nat -> CharRectangle
paddedRectangle height width
  = let row = padRow width [] in
    padCol height row [] where
      padRow : Nat -> (List Char) -> (List Char)
      padRow Z chars = chars
      padRow (S w) chars = ' ' :: (padRow w chars)

      padCol : Nat -> (List Char) -> CharRectangle -> CharRectangle
      padCol Z row chars = chars
      padCol (S h) row chars = row ::  (padCol h row chars)

||| heights are measured in numbers of lines, this is designed for
||| something like a command line console where we can't offset
||| by fractions of a line.
getHeight : CharRectangle -> Nat
getHeight [] = 0
getHeight (c::cs) = 1 + (getHeight cs)

||| widths are measured in number of characters, This is designed for
||| monospaced (fixed width) fonts so every character is the same
||| width and offsets of fractions of a character width are not
||| possible
getWidth : CharRectangle -> Nat
getWidth [] = 0
getWidth (c::cs) = length c

{-
||| pad with spaces to make rectangle a given height
||| try to pad equally at the top and bottom so that the content
||| remains in the middle. if this can't be done evenly then put
||| extra line at the top.
vpad : CharRectangle -> Nat -> CharRectangle
vpad a requiredHeight =
  -- if requiredHeight is already equal or greater than that
  -- required then return without changing
  if (getHeight(a) >= requiredHeight)
  then a
  else
    let
      -- work out ammount to padded
      deltaU:Union(NNI,"failed") := subtractIfCan(requiredHeight,getHeight(a))
      if deltaU case "failed" then return a
      delta:NNI := deltaU::NNI
      dR:Record(quotient:NNI,remainder:NNI) := divide(delta::NNI,2::NNI)$NNI
      topPadCount:NNI := dR.quotient
      if dR.remainder > 0 then topPadCount := topPadCount + 1
      bottomPadCount:NNI := dR.quotient
      paddedLine:List Character := [char(" ")]
      for x in 1..(getWidth(a)) repeat
        if x=1 then paddedLine := [char(" ")]
        else paddedLine := concat(paddedLine,char(" "))$List(Character)
      -- can I replace above 'for' loop with list comprehension?
      -- paddedLine:List Character := [char(" ") for x in [1..(getWidth(a)::NNI)]]
      newRectangle:List List Character := [paddedLine]
      for i in 1..topPadCount repeat
        if i=1 then newRectangle:= [paddedLine]
        else newRectangle := concat(newRectangle,paddedLine)$List(List(Character))
      for b in a repeat
        newRectangle := concat(newRectangle,b)$List(List(Character))
      for i in 1..bottomPadCount repeat
        newRectangle := concat(newRectangle,paddedLine)$List(List(Character))
      newRectangle::%
-}

