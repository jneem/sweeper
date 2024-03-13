#import "@preview/ctheorems:1.1.2": *
#set par(justify: true)

#show: thmrules
#let lemma = thmbox("lemma", "Lemma")
#let def = thmbox("definition", "Definition")
#let proof = thmproof("proof", "Proof")

We'll be talking about sweep line algorithms, where the sweep line is horizontal and increasing in $y$.
Therefore, every line segment "starts" at the coordinate with smaller $y$ and "ends" at the coordinate
with larger $y$ (we'll assume for now that there are no horizontal segments). We'll parametrize each
line segment as a function of $y$. So if $alpha: [y_0 (alpha), y_1 (alpha)] arrow bb(R)$ is a line segment
then $alpha(y)$ is the $x$ coordinate at $y$-coordinate $y in [y_0 (alpha), y_1 (alpha)]$

Define a relation $lt.curly_(y,epsilon)$ on line segments whose domain contains $y$, where
$alpha lt.curly_(y,epsilon) beta$ if $alpha(y) + epsilon < beta(y)$.
Despite our choice of symbol, this is not necessarily transitive.

#def[
  Suppose $alpha$ and $beta$ are two segments whose domain contains $y$. We say that *$alpha$ and $beta$
  are $epsilon$-close from $y$ onwards* if
  $ |alpha(z) - beta(z)| <= epsilon $
  for all $y <= z <= min(y_1(alpha), y_1(beta))$.
] <close_from_y_onwards>

== Partially ordered sweep-lines

At our first pass, we won't try to detect intersections at all. Instead, we'll produce
a continuum of sweep-lines (constant except at a finite number of points) that *approximately*
track the horizontal order of the segments.

#def[
The ordered collection $(alpha^1, ..., alpha^m)$ of line segments is #emph[$epsilon$-ordered at $y$]
if each $alpha^i$ has $y$ in its domain and $alpha^i lt.curly_(y,epsilon) alpha^j$ for all $1 <= i < j <= m$.
]

To be precise, our algorithm will produce a family of sweep-lines that are $epsilon$-ordered at every $y$
(and also #emph[complete] in the sense that the sweep-line at $y$ will contain all line segments whose
domain contains $y$). This seems weaker than finding all the intersections (for example, because if you
find all intersections you can use them to produce a completely ordered family of sweep-lines), but
in fact they're more-or-less equivalent. One way to see this is to note that intersection points
can be tracked (to within a horizontal $epsilon$) by checking when segments change order in the sweep-line.
But also, I'm pretty sure this is true:

#lemma[
If $(alpha^1, ..., alpha^m)$ is $epsilon$-ordered at $y$ then there exist $x^1 <= ... <= x^m$ such that
$|alpha^i (y) - x^i| <= epsilon$ for all $i$.
]

So once we have our family of approximate sweep-lines, we can go back and perturb the lines so that our
approximate ordering is exact.

One consequence of our approximate approach is that we need to do a little extra bookkeeping to maintain
the continuity of the input paths: when one segment exits and its path-neighbor enters, we need to remember
that they are connected because the approximate sweep-line might not keep them together. We'll ignore this
bookkeeping for now, and we'll also gloss over the fact that a real implementation would do everything in
one pass. (The goal here is to get into detail about the sweep-line invariants, and prove that we can maintain them.)

== The sweep-line invariants

We're going to have a sweep-line that depends on $y$. When we need to emphasize this, we'll use the
cumbersome but explicit notation
$(alpha_y^1, ..., alpha_y^(m_y))$.

#def[
Suppose $(alpha^1, ..., alpha^m)$ is $epsilon$-ordered at $y$.
We say that $alpha^j$ $epsilon$-crosses $alpha^i$ by $y'$ if $j < i$ and $alpha^j gt.curly_(y',epsilon) alpha^i$
or $i < j$ and $alpha^i gt.curly_(y',epsilon) alpha^j$.
]

In other words, an $epsilon$-crossing of two segments witnesses the $epsilon$-ordering invariant breaking.


Our sweep-line will maintain two invariants:
+ At every $y$, the sweep-line is $epsilon$-ordered at $y$. (We'll call this the "order" invariant.)
+ For every $y$, every $y' > y$, and every $1 <= i < j <= m_y$, if $alpha_y^i$ and $alpha_y^j$ $epsilon$-cross by $y'$,
  then the event queue contains an event for some $j' in (i, j)$,
  and at least one of these events occurs before $y'$.
  (We'll call this the "crossing" invariant.)

Hopefully the first invariant is already well-motivated, so let's discuss the second.
To naively ensure that we find
all intersections, we could adopt a stronger crossing invariant that requires all pairs of intersecting segments
in the sweep-line to immediately put an intersection event in the queue. This would be inefficient to maintain because
it would require testing all pairs of segments. The main Bentley-Ottmann observation is that it's enough to have intersection
events for all sweep-line-adjacent pairs, because any pair of lines will have to become sweep-line adjacent strictly
before they intersect. We can't rely only on sweep-line adjacency because of the $epsilon$ fudge, but our "crossing"
event essentially encodes the same property. Note that if $j = i+1$ and $y$ is just before the $epsilon$-crossing height and
there are no other segments nearby, then the mysterious $j'$ must be either $i$ or $j$ (because there is nothing in between)
and the mysterious queue event must be the crossing of $i$ and $j$ (it couldn't be an exit event, because we assumed they
cross and they must cross before they exit). In other cases, the crossing event ensures that even if we haven't
recorded the upcoming crossing of $alpha^i$ and $alpha^j$, something will happen in between them that will give us
a chance to test their crossing.

== Sweeping the sweep line

The first observation is that the sweep line invariants are maintained as we increase $y$ continuously up
to the next event:
+ For the order invariant, first note that there is an event whenever $y$ leaves the domain of a segment, so $y$ remains in all domains until the next event.
  Moreover, if at any $y' > y$ the ordering breaks, two line segments must have $epsilon$-crossed one another by $y'$.
  The third invariant guarantees that there's an event before this happens, so by the contra-positive until an event happens the ordering
  constraint is maintained.
+ This invariant is maintained because the set of things to check (i.e. the set of line segments that cross $epsilon$-cross
  one another after $y$) only shrinks as $y$ increases.

== Interaction with adjacent segments

In vanilla Bentley-Ottmann, each segment gets compared to its two sweep-line neighbors; they can either intersect or not intersect.
When numerical errors are taken into account, we may need to compare to
more segments. Also there are more possible results from the comparison.

First of all, there are two kinds of intersections: a "normal" intersection where we can compute the
`y` coordinate of the crossing and insert an intersection event into the queue; and another kind of intersection
where the two lines definitely intersect somewhere, but they're too close to coincident to really figure out when.
We call the first case a "clear" intersection and the second case a "shuffle" intersection.
Rather than defining exactly the distinction between the two cases, let's list some properties that we
would like to hold.

Fix $y$ and suppose we have two segments $alpha^1$ and $alpha^2$ satisfying $alpha^1 lt.curly_(y,epsilon) alpha^2$.
- If the segments $epsilon$-cross then they have a clear intersection or a shuffle intersection (or both).
- If they have a shuffle intersection then the two segments are $epsilon$-close from $y$ onwards
  (@close_from_y_onwards).
- If the segments clearly intersect, there is an algorithm that computes a lower bound $hat(y)$ on the exact intersection height,
  with the property that $alpha^1(hat(y)) >= alpha^2(hat(y)) - epsilon$.

The second property implies that if there's a shuffle intersection $alpha^1$ and $alpha^2$ can be in either order
in the sweep-line (for all sweep-lines at or after $y$).

The third property imposes a requirement on the allowable slopes for $alpha^1$ and $alpha^2$. With finite precision
and almost-horizontal lines, such a $hat(y)$ might not exist. The current implementation has some special logic
for exactly horizontal lines (which is not yet written up here), and deals with almost-horizontal lines by perturbing
them to be exactly horizontal. The reason we insist on a lower bound will become clear later.

The other thing we need to check when comparing adjacent segments is whether we're allowed to "stop:" once we've
compared $alpha^j$ to $alpha^(i)$, do we also need to compare it to $alpha^(i-1)$? If so, we say that $alpha^i$ "ignores"
$alpha^j$; otherwise, we say that $alpha^i$ "blocks" $alpha^j$.

== An "enter" event

When inserting a new segment into the current sweep-line, we first choose its sweep-line position using
a binary search on its horizontal coordinate. Let's write $(alpha^1, dots, alpha^m)$ for the sweep-line
*after* inserting the new segment $alpha^i$.

#lemma[
$(alpha^1, dots, alpha^m)$ are $epsilon$-ordered at $y$.
]

#proof[
Binary search on unsorted lists is a bit funky, but it is still guaranteed to insert $alpha^i$ in a position
where $alpha^(i-1) (y) <= alpha^i (y) <= alpha^(i+1) (y)$ (where the boundary cases are handling by declaring that
"$alpha^0(y)$" means $-infinity$ and "$alpha^(m+1) (y)$" means $infinity$).
So now consider any $j != i$. Since the sweep-line was $epsilon$-ordered before inserting $alpha^i$, if $j >= i + 1$ then
$alpha^(i) (y) <= alpha^(i+1) (y) <= alpha^j (y) + epsilon$.
On the other hand, if $j <= i - 1$ then $alpha^j (y) - epsilon <= alpha^(i-1) (y) <= alpha^i (y)$. This checks the ordering
invariant when one of the indices being compared is the newly-inserted one. Clearly the ordering invariant
is also maintained when both indices being compared are old.
]

Next we need to look for intersections; we'll look to the left first and then to the right.
We start by comparing $alpha^i$ to $alpha^(i-1)$.
If they clearly intersect, we add an intersection event to the queue. If they have a shuffle intersection,
we change their order in the current sweep line. Then if $alpha^(i-1)$ blocks $alpha^i$, we stop comparing to the left;
otherwise, we continue to look at $alpha^(i-2)$.
(If we compare $alpha^j$ to $alpha^i$ and there is a shuffle intersection, we move $alpha^i$ to the left of $alpha^j$
while preserving the order of any segments between them.) (TODO: consider rewriting this algorithm as a search for
the position of the new segment, instead of as an insertion followed by an iterative modification)

#lemma[
For any sweep-line  $(alpha^1, dots, alpha^m)$ that is $epsilon$-ordered at $y$ and any $i < j < k$, if $alpha^i$ and $alpha^j$
have a shuffle intersection then $alpha^j$ and $alpha^k$ do not have a shuffle intersection.
]

#proof[
TODO. We need to tweak the definition of shuffle intersections to ensure this. The point is that if we've shuffled to the
left after the initial insertion, we need to make sure that we don't also try to shuffle to the right.
I think it should be enough to insist that shuffle intersections only happen when the two segments are in the wrong (exact)
order at height $y$.
]
