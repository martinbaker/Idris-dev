||| outputs mathematical structures in more human readible way.
module outputForm

import public Data.Vect -- from base package
import public Data.Matrix -- from contrib package

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

||| Overwrite a character in a given coordinate of a CharRectangle.
seteltChar : CharRectangle -> Char -> Nat -> Nat -> CharRectangle
seteltChar a c offsetx offsety = setLine a c offsetx offsety Z [] where
  setEle : (List Char) -> Char -> Nat -> Nat -> (List Char) -> (List Char)
  setEle [] c offsetx n res = reverse res
  setEle (ele::eles) c offsetx n res =
    if n==offsetx
    then setEle eles c offsetx (S n) (c::res)
    else setEle eles c offsetx (S n) (ele::res)

  setLine : CharRectangle -> Char -> Nat -> Nat -> Nat -> CharRectangle -> CharRectangle
  setLine [] c offsetx offsety n res = reverse res
  setLine (cr::crs) c offsetx offsety n res =
    if n==offsety
    then setLine crs c offsetx offsety (S n) ((setEle cr c offsetx Z [])::res)
    else setLine crs c offsetx offsety (S n) (cr::res)

||| Embed b into a offset by the given coordinates
||| replacing whatever is there.
||| @a input rectangle
||| @b replacement rectangle
||| @minx x coordinate of replacement in input
||| @miny y coordinate of replacement in input
setSubRectangle : (a:CharRectangle) -> (b:CharRectangle) ->
                  (minx:Nat) -> (miny:Nat) -> CharRectangle
setSubRectangle a b minx miny =
  let maxx = minx + (getWidth b)
      maxy = miny + (getHeight b)
  in
    setLine a b minx maxx miny maxy Z Z []
  where
    -- @ input row
    -- @ replacement row
    -- @ minx in input
    -- @ maxx in input
    -- @ n=position in input
    -- @ m=position in replacement
    -- @ res=result being built up
    setEle : (List Char) -> (List Char) -> Nat -> Nat -> Nat -> Nat -> (List Char) -> (List Char)
    setEle [] c minx maxx n m res = reverse res
    setEle (ele::eles) c minx maxx n m res =
      let mnewEle = if (n == minx) then (index' Z c) else (index' m c)
          newEle = case mnewEle of
            Just x => x
            Nothing => 'e'
      in
        if (n == minx)
        then setEle eles c minx maxx (S n) 1 (newEle::res)
        else
          if (n >= minx) && (n < maxx)
          then setEle eles c minx maxx (S n) (S m) (newEle::res)
          else setEle eles c minx maxx (S n) (S m) (ele::res)

    -- @ input rectangle
    -- @ replacement rectangle
    -- @ minx in input
    -- @ maxx in input
    -- @ miny in input
    -- @ maxy in input
    -- @ n=row number in input
    -- @ m=row number in replacement
    -- @ res=result being built up
    setLine : CharRectangle -> CharRectangle -> Nat -> Nat ->
              Nat -> Nat -> Nat -> Nat -> CharRectangle -> CharRectangle
    setLine [] b minx maxx miny maxy n m res = reverse res
    setLine (cr::crs) b minx maxx miny maxy n m res =
      let mnewLine = if (n == miny) then index' Z b else index' m b
          newLine = case mnewLine of
            Just x => x
            Nothing => ['f']
      in
        if (n == miny)
        then setLine crs b minx maxx miny maxy (S n) 1 ((setEle cr newLine minx maxx Z Z [])::res)
        else
          if (n >= miny) && (n < maxy)
          then setLine crs b minx maxx miny maxy (S n) (S m) ((setEle cr newLine minx maxx Z Z [])::res)
          else setLine crs b minx maxx miny maxy (S n) (S m) (cr::res)

||| Draw vertical line of given height
vLine : Nat -> Bool -> CharRectangle
vLine Z first = []
vLine (S n) first = if (n==Z) || first
              then ['+'] :: (vLine n False)
              else ['|'] :: (vLine n False)

||| Draw horizontal line of given width
hLine : Nat -> (List Char)
hLine Z = []
hLine (S n) = '-' :: (hLine n)


||| Draw a line to left, right, top and/or bottom given rectangle
line : CharRectangle -> Bool -> Bool -> Bool -> Bool -> CharRectangle
line cr left right top bottom =
  if (left || right) && (top || bottom)
  then lineLR (lineTB cr top bottom) left right
  else
    if (left || right)
    then lineLR cr left right
    else lineTB cr top bottom
      where
        ||| Draw a line to left, right or both of given rectangle
        lineLR : CharRectangle -> Bool -> Bool -> CharRectangle
        lineLR cr left right =
          let height = getHeight cr
              hl = vLine height True
          in if (left && right)
             then hConcat [hl,cr,hl]
             else if left
                  then hConcat [hl,cr]
                  else hConcat [cr,hl]

        ||| Draw a line to top, bottom or both of given rectangle
        lineTB : CharRectangle -> Bool -> Bool -> CharRectangle
        lineTB cr top bottom =
          let width = getWidth cr
              vl = [hLine width]
          in if (top && bottom)
             then vConcat [vl,cr,vl]
             else if top
                  then vConcat [vl,cr]
                  else vConcat [cr,vl]

||| generates a string for each line. Trailing spaces are stripped
||| off the end of each line.
stringise : CharRectangle -> (List String)
stringise [] = []
stringise (a::as) =
  (reverse (ltrim (reverse (pack a)))) :: (stringise as)

||| Output a rectangle to console
output : CharRectangle -> IO ()
output [] = putStrLn ""
output (cr::crs) = do
  putStrLn (pack cr)
  output crs

-- test with :exec output test2

------------------------------------------------------------------------------------

--interface OutputFormatExpression where

||| This holds only enough information about the expression to display it.
||| Semantic and type information is dropped to make it general enough to be
||| output in many forms.
data OutputFormat : Type where
  ||| integer number
  OFInt : Integer -> OutputFormat
  ||| floating point (real) number
  OFFloat : Double -> OutputFormat
  ||| text without quotation marks
  OFSymbol : String -> OutputFormat
  ||| text with quotation marks
  OFString : String -> OutputFormat
  ||| a unary operation (prefix or postfix)
  OFUnaryOp : String -> OutputFormat -> OutputFormat
  ||| a binary operation
  OFBinaryOp : String -> OutputFormat -> OutputFormat -> OutputFormat
  ||| vertically separated expressions
  OFVConcat : (List OutputFormat) -> OutputFormat
  ||| horizontally separated expressions
  OFHConcat : (List OutputFormat) -> OutputFormat
  ||| a 2D grid of expressions
  OFGrid : (List (List OutputFormat)) -> OutputFormat
  ||| draw a line on left,right,top or bottom of given rectangle
  OFLine : OutputFormat -> Bool -> Bool -> Bool -> Bool -> OutputFormat

------------------------------------------------------------------------------------

display : OutputFormat -> IO ()
display f = output (dispMono f) where
  dispMono : OutputFormat -> CharRectangle
  dispMono (OFInt i) = charRectangle (show i)
  dispMono (OFFloat d) = charRectangle (show d)
  dispMono (OFSymbol s) = [unpack s]
  dispMono (OFString s) = [unpack ("\"" ++ s ++ "\"")]
  dispMono (OFUnaryOp s f) = hConcat [charRectangle s, charRectangle " ",dispMono f]
  dispMono (OFBinaryOp s f1 f2) = hConcat [dispMono f1, charRectangle " ",charRectangle s,
                                           charRectangle " ",dispMono f2]
  dispMono (OFLine f l r t b) = line (dispMono f) l r t b
  dispMono (OFVConcat lst) = vConcat (map dispMono lst)
  dispMono (OFHConcat lst) = hConcat (map dispMono lst)
  dispMono (OFGrid lst2) = gridConcat (opf2cd lst2) where
    opf2cd : (List (List OutputFormat)) -> (List (List CharRectangle))
    opf2cd [] = []
    opf2cd (lst::lsts) = (map dispMono lst)::(opf2cd lsts)

-- run using: :exec test5
test5 : IO ()
test5 =
  let a = OFSymbol "a"
      bcdef =OFSymbol "bcdef"
      ghi =OFSymbol "ghi"
      left = OFVConcat [a,bcdef,ghi]
      right = OFSymbol "xyz"
  in
    display (OFLine (OFHConcat [left,right]) True True False False)

------------------------------------------------------------------------------------

||| An expression which can hold both numeric and symbolic values.
||| Initially needs to support ring interface, that is, at least '+' and '*'
||| Really I would want this to be a very general expression like 'PTerm'
||| in Idris-dev/src/Idris/AbsSyntaxTree.hs but with ability to have
||| ring, field or group interfaces and to support custom appearance of
||| types (example a + i b for complex types).
data MyExpression : Type where
  MyVar : String -> MyExpression
  MyInt : Integer -> MyExpression
  MyFloat : Double -> MyExpression
  (<+>) : MyExpression -> MyExpression -> MyExpression
  (<*>) : MyExpression -> MyExpression -> MyExpression

||| Need to implement parenthesis based on precedence
implementation Show MyExpression where
  show (MyVar s) = s
  show (MyInt n) = show n
  show (MyFloat n) = show n
  show (a <+> b) = (show a) ++ "+" ++ (show b)
  show (a <*> b) = (show a) ++ "*" ++ (show b)

implementation Num MyExpression where
  (+) a b = a <+> b
  (*) a b = a <*> b
  fromInteger i = MyInt i

------------------------------------------------------------------------------------
||| Construct a matrix from a list of lists without knowing,
||| in advance, the dimensions of the matrix.
||| Needs to be improved, handles the situation
||| where inner lists are different lengths badly.
||| Can this be properly typechecked.
matrix : (List (List ty)) -> (n ** (m ** Matrix n m ty))
matrix a =
  let h = length a
      w = arrayWidth a
  in (h ** (w ** (matrix' h w (myMap a w)))) where
    ||| Assume all inner lists are the same length
    ||| so just get the width of the first
    arrayWidth : (List (List ty)) -> Nat
    arrayWidth [] = Z
    arrayWidth (w::ws) = length w

    ||| convert the inner list to vectors
    myMap : List (List ty) -> (m:Nat) -> List (Vect m ty)
    myMap [] m = []
    myMap (x::xs) m =
      case exactLength m (fromList x) of
        Nothing => (myMap xs m)
        Just v => (v :: (myMap xs m))

    ||| convert the outer list to vectors
    ||| inner list has already been converted by myMap
    ||| @ n number of rows
    ||| @ m number of columns
    matrix' : (n:Nat) -> (m:Nat) -> (List (Vect m ty)) -> (Matrix n m ty)
    matrix' Z m [] = the (Vect Z (Vect m ty)) Nil
    matrix' (S n) m (v::vs) =
      (v::(matrix' n m vs))

------------------------------------------------------------------------------------

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

||| temp test code
test3 : CharRectangle
test3 = setSubRectangle test2 (charRectangle "pqr") 2 2

