Algebra Library for Idris
-------------------------
The objective here is to build up a comprehensive library of algebraic code.
This should be designed so that each type of algebra interworks with all
the other algebras in a consistent way and each has a comprehensive set of proofs.

This is not just about computing arithmetic but also about having variables
in expressions and equations, computing with these expressions and
equations, also more abstract forms of algebra.

As a foundational theory this should be based on type theory with the types
defined in this library code corresponding as closely as possible to the
mathematical types being modeled.

Some of the ideas for this come from an existing open source CAS (Computer Algebra
System) called 'Axiom' and a fork of this called 'FriCAS'. Like Idris this
code also uses dependent types but it is more imperative in style, therefore
the code here is not a direct translation but does borrow some ideas.

In order to evaluate Idris as a basis for building such a library I have
chosen some diverse algebra topics to try things out:

fieldExpression.idr
-------------------
In order to implement an algebra our expressions and equations
need to work with mathematical variables. Note these variables
are different from variables in a program, for instance,
'y = 2*x' does not mean 'take the current value of x, multiply
it by 2 and assign this value to y' instead it means 'x and y
can range over any values as long as y is always twice x'.

Ideally I would want to have an expression over mixed types.
For instance I would like have Doubles and Integers in the
same expression, also vectors and scalars in the same
expression, in fact any mathematically valid combination
of types.

So I would like to generalise the current implementation
from an 'Expression over a field' to 'Expression over a
mathematical type'. However
this means that, for instance,  the (/) is not valid for
certain types so we want to bar that operator for types
where it is not valid. Also these types would not implement
the Fractional interface and so on.

I don't know how to code this so the Idris type system could
allow and disallow these things for each mathematical type
in the expression.

Another enhancement that I would like is to code variables
using de Bruijn indexes as in 'The Well-Typed Interpreter'
example here:
http://docs.idris-lang.org/en/latest/tutorial/interp.html


quaternion.idr
-------------
In most cases Quaternion will be defined over Reals (In computer terms
floating point - Double), an important application is to calculate finite
rotations in 3 dimensional space.
However, mathematically it can be defined over rings (such as Integers) so
a more general data definition would be:
data Quaternion Neg => a = Quat a a a a
This would make definition more compatible with Data.Complex
I am tempted to define the quaternion like this:
data Quaternion r = Quat r r r r
as it looks more efficient (but perhaps I'm still thinking in
a Java style). The following seems more like Idris style?
data Quaternion r= RealAxis r | I r | J r | K r | (++) (Quaternion r) (Quaternion r) 


perm.idr
--------
Implements permutations (subgroups of bijections of a set).
Represents the permutation p as a list of preimages and images, i.e
p maps preimage to image for all indices k. Elements of set not
in preimage are fixed points, and these are the only fixed points
of the permutation.


Further Information
-------------------

For further information see:<ul>
  <li>the documentation here: http://www.euclideanspace.com/prog/idris/</li>
  <li>and the code here: https://github.com/martinbaker/Idris-dev</li>
</ul>

