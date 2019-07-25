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

||| Constructor to create single line rectangle
charRectangle : String -> CharRectangle
charRectangle a = [unpack a]

||| Constructor to create rectangle with an array of empty spaces.
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

||| get maximum height from a list of rectangles
getMaxHeight : (List CharRectangle) -> Nat -> Nat
getMaxHeight [] runningMax = runningMax
getMaxHeight (c::cs) runningMax  =
  if (getHeight c) > runningMax
  then getMaxHeight cs (getHeight c)
  else getMaxHeight cs runningMax

||| Widths are measured in number of characters, This is designed for
||| monospaced (fixed width) fonts so every character is the same
||| width and offsets of fractions of a character width are not
||| possible
getWidth : CharRectangle -> Nat
getWidth [] = 0
getWidth (c::cs) = length c

||| Pad with spaces to make rectangle a given height
||| try to pad equally at the top and bottom so that the content
||| remains in the middle. if this can't be done evenly then put
||| extra line at the top.
||| If requiredHeight is already equal or greater than that
||| required then return without changing.
vpad : CharRectangle -> Nat -> CharRectangle
vpad a requiredHeight =
  let delta = minus requiredHeight (getHeight a)
      topPadCount = divNat delta 2
      bottomPadCount = topPadCount
      topPadOdd = modNat delta 2
      topPadCount = if (isZero topPadOdd) then topPadCount else topPadCount+1
      width = getWidth a
  in
    if isZero delta
    then a
    else reverse (padLineNTimes bottomPadCount width (reverse (padLineNTimes topPadCount width a)))
  where
      padLine : Nat -> (List Char) -> (List Char)
      padLine Z chars = chars
      padLine (S w) chars = ' ' ::  (padLine w chars)

      padLineNTimes : Nat -> Nat -> CharRectangle -> CharRectangle
      padLineNTimes Z w chars = chars
      padLineNTimes (S h) w chars = (padLine w []) :: (padLineNTimes h w chars)

||| Pad with spaces to make rectangle a given width
||| try to pad equally on the left and right so that the content
||| remains in the middle. if this can't be done evenly then put
||| extra line on the right.
||| If requiredWidth is already equal or greater than that
||| required then return without changing.
hpad : CharRectangle -> Nat -> CharRectangle
hpad a requiredWidth =
  let delta = minus requiredWidth (getWidth a)
      rightPadCount = divNat delta 2
      leftPadCount = rightPadCount
      topPadOdd = modNat delta 2
      rightPadCount = if (isZero topPadOdd) then rightPadCount else rightPadCount+1
      hight = getHeight a
  in
    if isZero delta
    then a
    else padLines leftPadCount rightPadCount a []
  where
      padPartLine : Nat -> (List Char)
      padPartLine Z = []
      padPartLine (S n) = ' ' :: (padPartLine n)

      padLine : Nat -> Nat -> (List Char) -> (List Char)
      padLine nleft nright lin = (padPartLine nleft) ++ lin ++ (padPartLine nright)

      padLines : Nat -> Nat -> CharRectangle -> CharRectangle -> CharRectangle
      padLines nleft nright [] res = []
      padLines nleft nright (lin :: lins) res = (padLine nleft nright lin)::res

{-
||| vertical concatination of rectangles produces a new rectangle
||| consisting of all the supplied rectangles, one above the other.
||| The order of the list is assumed to be top to bottom.
||| Concatinated rectangles don't have to match in either width or
||| height. The values will all be increased to the value of the
||| biggest and padded so that they are centred.
vconcat : (List CharRectangle) -> CharRectangle
vconcat a =
  -- first we calculate the maximum width and height of all then
  -- rectangles to be concatinated.
  let maxWidth = 
      maxWidth:NNI := 0
      maxHeight:NNI := 0
      for x in a repeat
        w := getWidth(x)
        h := getHeight(x)
        if w > maxWidth then maxWidth:= w
        if h > maxHeight then maxHeight:= h
      res:List List Character := empty()$List(List(Character))
      -- go through each input rectangle and pad them out to
      -- the same width
      -- put all the rows on after the other.
      for x in a repeat
        paddedIn:% := hpad(x,maxWidth)
        for y in paddedIn repeat -- 'y' is a row
          -- so 'res' contains the rows in all the inputs
          res := concat(res,y)$List(List(Character))
      res::%
-}
