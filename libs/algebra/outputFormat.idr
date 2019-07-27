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

||| get maximum width from a list of rectangles
getMaxWidth : (List CharRectangle) -> Nat -> Nat
getMaxWidth [] runningMax = runningMax
getMaxWidth (c::cs) runningMax  =
  if (getWidth c) > runningMax
  then getMaxWidth cs (getWidth c)
  else getMaxWidth cs runningMax

||| For a grid produce a list of the width of each column.
getMaxWidths : (List (List CharRectangle)) -> (List Nat)
getMaxWidths grid = reverse (gmw (transpose grid) []) where
    gmw : (List (List CharRectangle)) -> (List Nat) -> (List Nat)
    gmw [] wl = wl
    gmw (g::gs) wl = gmw gs ((getMaxWidth g Z)::wl)

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

||| vertical concatenation of rectangles produces a new rectangle
||| consisting of all the supplied rectangles above each other.
||| The order of the list is assumed to be top to bottom.
||| Concatenated rectangles don't have to match in either width or
||| height. The values will all be increased to the value of the
||| biggest and padded so that they are centred.
vConcat : (List CharRectangle) -> CharRectangle
vConcat a =
  -- first we calculate the maximum width of all
  let maxWidth = getMaxWidth a Z
  in
      mergeIn a maxWidth []
  where
      mergeIn : (List CharRectangle) -> Nat -> CharRectangle -> CharRectangle
      mergeIn [] width cr = cr
      mergeIn (c::cs) width cr = mergeIn cs width (cr ++ (hpad c width))

||| horizontal concatenation of rectangles produces a new rectangle
||| consisting of all the supplied rectangles, side by side.
||| The order of the list is assumed to be left to right.
||| Concatenated rectangles don't have to match in either width or
||| height. The values will all be increased to the value of the
||| biggest and padded so that they are centred.
hConcat : (List CharRectangle) -> CharRectangle
hConcat a =
  -- first we calculate the maximum height of all.
  let maxHeight = getMaxHeight a Z
  in
    mergeIn a maxHeight []
  where
    sideBySide : CharRectangle -> CharRectangle -> CharRectangle -> CharRectangle
    sideBySide [] [] c = c
    sideBySide [] (right::rights) c = sideBySide [] rights (right :: c)
    sideBySide (left::lefts) [] c = sideBySide lefts [] (left :: c)
    sideBySide (left::lefts) (right::rights) c =
      sideBySide lefts rights ((left ++ (' '::right)) :: c)

    mergeIn : (List CharRectangle) -> Nat -> CharRectangle -> CharRectangle
    mergeIn [] height cr = cr
    mergeIn (c::cs) height cr = mergeIn cs height (reverse (sideBySide cr (vpad c height) []))

||| Grid concatenation.
||| Building an array of rectangles can't always be done by doing
||| vConcat first and then hConcat, or the other way round,
||| because they will be aligned vertically but not horizontally
||| or aligned horizontally but not vertically. So we need this
||| when we want to align in both dimensions simultaneously.
||| The valid modes are:
|||   "PLAIN"::Symbol no boundary
|||   "MATRIX"::Symbol boundary of 1 and left+right brackets
gridConcat : (List (List CharRectangle)) -> CharRectangle
gridConcat a =
  -- first we calculate a list of the width of each column
  let maxWidths = getMaxWidths a
  in
    gc a maxWidths []
  where
    sideBySide : CharRectangle -> CharRectangle -> CharRectangle -> CharRectangle
    sideBySide [] [] c = c
    sideBySide [] (right::rights) c = sideBySide [] rights (right :: c)
    sideBySide (left::lefts) [] c = sideBySide lefts [] (left :: c)
    sideBySide (left::lefts) (right::rights) c =
      sideBySide lefts rights ((left ++ (' '::right)) :: c)

    mergeInRow : (List CharRectangle) -> Nat -> (List Nat) -> CharRectangle -> CharRectangle
    mergeInRow [] height widths cr = cr
    mergeInRow (c::cs) height [] cr =
      mergeInRow cs height [] (reverse (sideBySide cr (vpad c height) []))
    mergeInRow (c::cs) height (w::ws) cr =
      mergeInRow cs height ws (reverse (sideBySide cr (hpad (vpad c height) w) []))

    gc : (List (List CharRectangle)) -> (List Nat) -> CharRectangle -> CharRectangle
    gc [] mw res = res
    gc (g::gs) mw res = res ++ (gc gs mw (mergeInRow g (getMaxHeight g Z) mw []))

||| temp test code
test : CharRectangle
test =
  let a = charRectangle "a"
      bcdef =charRectangle "bcdef"
      ghi =charRectangle "ghi"
      left = vConcat [a,bcdef,ghi]
      right = charRectangle "xyz"
  in
    hConcat [left,right]

||| temp test code
test2 : CharRectangle
test2 =
  let a = charRectangle "a"
      bcdefg =charRectangle "bcdefg"
      ghi =charRectangle "ghi"
      left = vConcat [a,bcdefg,ghi]
      right = charRectangle "xyz"
  in
    gridConcat [[a,right],[ghi,left]]
