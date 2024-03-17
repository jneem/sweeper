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

#def[
  Suppose $alpha$ and $beta$ are two segments whose domain contains $y$. We say that *$(alpha, beta)$
  $epsilon$-cross by $y$* if $y$ belongs to both domains and $alpha(y) > beta(y) + epsilon$.
  We say that *$(alpha, beta)$ $epsilon$-cross* if they $epsilon$-cross by $min(y_1 (alpha), y_1 (beta))$.
]

Note that the definition of $epsilon$-crossing is not symmetric: $(alpha, beta)$ $epsilon$-crossing is
not the same as $(beta, alpha)$ $epsilon$-crossing. We will usually talk about $(alpha, beta)$ $epsilon$-crossing
in the context that $alpha lt.curly_(y,epsilon) beta$, and in this context "$(alpha, beta)$ $epsilon$-cross" means
that at some height $y'$ before the end of $alpha$ and $beta$, the inequality $alpha lt.curly_(y',epsilon) beta$ will fail.

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

Our sweep-line will maintain three invariants:
+ At every $y$, the sweep-line is $epsilon$-ordered at $y$. (We'll call this the "order" invariant.)
+ For every $y$, every $y' > y$, and every $1 <= i < j <= m_y$, if $alpha_y^i$ and $alpha_y^j$ $epsilon$-cross by $y'$,
  then the event queue contains an event for some $j' in (i, j)$,
  and at least one of these events occurs before $y'$.
  (We'll call this the "crossing" invariant.)
+ For every $y$ and every $1 <= i < j <= m_y$, $(alpha^i, alpha^j)$ do not have a shuffle intersection at $y$.
  (We'll call this the "shuffling" invariant.)

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

I don't have a good self-contained motivation for the shuffling invariant yet, but it's hard to insert segments without it.

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
- If the segments clearly intersect, there is an algorithm that computes a lower bound $hat(y)$ on the exact intersection height,
  with the property that $alpha^1(hat(y)) >= alpha^2(hat(y)) - epsilon$.

The second property implies that if there's a shuffle intersection $alpha^1$ and $alpha^2$ can be in either order
in the sweep-line (for all sweep-lines at or after $y$).

The third property imposes a requirement on the allowable slopes for $alpha^1$ and $alpha^2$. With finite precision
and almost-horizontal lines, such a $hat(y)$ might not exist. The current implementation has some special logic
for exactly horizontal lines (which is not yet written up here), and deals with almost-horizontal lines by perturbing
them to be exactly horizontal. The reason we insist on a lower bound will become clear later.

Now let's try to come up with definitions that satisfy our properties:
#def[
Suppose $alpha lt.curly_(y,epsilon) beta$.
We say that *$(alpha, beta)$ have a shuffle intersection at $y$* if $beta(y) < alpha(y)$ and $(alpha, beta)$ $epsilon$-cross.
We say that *$(alpha, beta)$ have a clear intersection at $y$* if $(alpha, beta)$ $epsilon$-cross but do not have a shuffle intersection at $y$.
]

Clearly these definitions satisfy the first desired property (if $(alpha, beta)$ $epsilon$-cross then there is some kind
of intersection). To check that they satisfy the second property requires some more careful analysis (which will only
work when $epsilon$ is sufficiently large depending on the precision of the floating point numbers we're using),
but the point is that if $(alpha, beta)$ clearly cross then their "slopes" (not exactly their slopes, but close enough)
are at least $epsilon$ apart and so we can compute intersections accurately enough. In practice, there will be some numerical
errors in evaluating these definitions, but that's ok in some cases: if $beta(y)$ is just barely less than $alpha(y)$, we
can allow a false negative in the shuffle intersection test, and the numerical stability for the clear intersection
test will just be a little bit worse. On the other hand, we will insist that if the shuffle intersection test passes
then $beta(y)$ is truly less than $alpha(y)$.

#lemma[
If $(alpha, beta)$ have a shuffle intersection at $y$ then $alpha(y') > beta(y')$ for all $y' in [y, min(y_1 (alpha), y_1 (beta))]$.
]<lem-shuffle-ordered>

#proof[
The definition of shuffle intersections implies that the desired inequality holds at the endpoints of the interval. Convexity
(or monotonicity of linear functions) does the rest.
]

#lemma[
Suppose $(alpha, beta, gamma)$ is $epsilon$-ordered at $y$. If $(alpha, beta)$ have a shuffle intersection at $y$ and $(beta, gamma)$
have a shuffle intersection at $y$ then $(alpha, gamma)$ have a shuffle intersection at $y$.
]<lem-shuffle-transitive>

#proof[
Let $y_1 = min(y_1 (alpha), y_1 (beta), y_1(gamma))$.
Since $alpha$ and $beta$ have a shuffle intersection at $y$, $alpha(y) > beta(y)$; since $beta$ and $gamma$ have a shuffle
intersection at $y$, $beta(y) > gamma(y)$; therefore, $alpha(y) > gamma(y)$.
Now, $y_1 = min(y_1(alpha), y_1(beta))$ or $y_1 = min(y_1(beta), y_1(gamma))$; in the first case
$alpha(y_1) > beta(y_1) + epsilon$; in the second case $beta(y_1) > gamma(y_1) + epsilon$. In either case, @lem-shuffle-transitive
implies that $alpha(y_1) > beta(y_1) > gamma(y_1)$. Putting these cases together, we have $alpha(y_1) > gamma(y_1) + epsilon$.

Finally, we assumed that $(alpha, beta, gamma)$ is $epsilon$-ordered at $y$ and so $alpha(y) <= gamma(y) + epsilon$.
It follows that $alpha - gamma$ is monotonic increasing, and so $(alpha, gamma)$ $epsilon$-cross. Therefore $(alpha, gamma)$
have a shuffle intersection at $y$.
]

== An "enter" event

When inserting a new segment into the current sweep-line, we first choose its sweep-line position using
a binary search on its horizontal coordinate. Let's write $(alpha^1, dots, alpha^m)$ for the sweep-line
before inserting the new segment, and let's call the new segment $beta$. First, we observe that
there is a place to insert the new segment while preserving the ordering invariant.

#lemma[
Suppose $(alpha^1, ..., alpha^m)$ is $epsilon$-ordered at $y$.
If $alpha^i (y) <= beta(y) <= alpha^(i+1) (y)$ then
$(alpha^1, ..., alpha^i, beta, alpha^(i+1), ..., alpha^m)$ are $epsilon$-ordered at $y$.
(Here, we can allow the corner cases $i = 0$ and $i = m$ by declaring that
"$alpha^0(y)$" means $-infinity$ and "$alpha^(m+1) (y)$" means $infinity$).
]<lem-insert-preserving-order>

#proof[
Since $(alpha^1, ..., alpha^m)$ was $epsilon$-ordered at $y$, it suffices to compare beta with all $alpha^j$.
So now fix $1 <= j <= m$. If $j >= i + 1$ then
$beta (y) <= alpha^(i+1) (y) <= alpha^j (y) + epsilon$ (where the last inequality follows because $(alpha^1, ..., alpha^m)$ is $epsilon$-ordered.
On the other hand, if $j <= i$ then $alpha^j (y) - epsilon <= alpha^i (y) <= beta (y)$.
]

(Note that the inequalities $alpha^i (y) <= beta(y) <= alpha^(i+1) (y)$ need to be exact for the proof to work.
In the face of inexact computations, we might need to do some extra work. It becomes tricky if there are segments near $beta$
that almost violate the ordering invariant, but we could detect that situation and add an extra clean-up step.)

@lem-insert-preserving-order implies that we can insert a new segment while preserving the ordering invariant. To help
with the other invariants, we look for shuffle intersections. By @lem-shuffle-transitive and the shuffling invariant
for the old sweep-line, there cannot be shuffle intersections "on both sides" of $beta$: if $j <= i < k$ then
$(alpha^j, beta)$ and $(beta, alpha^k)$ cannot both have shuffle intersections (because then @lem-shuffle-transitive would
imply that $(alpha^j, alpha^k)$ have a shuffle intersection, violating the shuffling invariant). So there are three cases:

- If $beta$ has no shuffle intersections, insert it between $alpha^i$ and $alpha^(i+1)$. This preserves the shuffling invariant trivially.
- If $beta$ has a shuffle intersection with some $j <= i$, take the smallest such $j$ and insert $beta$ between $alpha^(j-1)$ and $alpha^j$.

  To see that this preserves the ordering invariant, recall that $(alpha^1, ..., alpha^i, beta, alpha^(i+1), ..., alpha^m)$ satisfies the
  ordering invariant and so we only need to check that $beta lt.curly_(y,epsilon) alpha^k$ for $k = j, ..., i$. But this follows from the
  fact that $alpha^j lt.curly_(y,epsilon) alpha^k$ for all such $k$, combined with $beta(y) < alpha^j (y)$ (which holds because $(alpha^j, beta)$
  had a shuffle intersection at $y$).

  To see that this preserves the shuffling invariant, our choice of $j$ ensures that $(alpha^k, beta)$ doesn't shuffle-intersect for any $k < j$.
  On the other hand, @lem-shuffle-transitive and the shuffling invariant for the old sweep-line imply that $(beta, alpha^k)$ doesn't
  shuffle-intersect for any $k > j$.
- If $beta$ has a shuffle intersection with some $j >= i + 1$, take the largest such $j$ and insert $beta$ between $alpha^j$ and $alpha^(j+1)$.
  By analogous logic to the previous case, this position for $beta$ preserves the ordering and shuffling invariants.

Now that we've found a position for $beta$, we need to test it for clear intersections.
