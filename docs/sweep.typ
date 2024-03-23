#import "@preview/ctheorems:1.1.2": *
#set par(justify: true)

#show: thmrules
#let lemma = thmbox("lemma", "Lemma")
#let def = thmbox("definition", "Definition")
#let proof = thmproof("proof", "Proof")

#let inexact(term) = {
  block(inset: 16pt,
    block(
      inset: 16pt,
      stroke: 1pt + gray,
      radius: 12pt,
      text(
        size: 10pt,
        [Note for inexact arithmetic: #term]
      )
    )
  )
}

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
+ For every $y$ and every $1 <= i < j <= m_y$, if $alpha_y^i$ and $alpha_y^j$ $epsilon$-cross
  then the event queue contains an event between $i$ and $j$,
  and at least one of these events occurs before the $epsilon$-crossing height, or at $y$.
  (We'll call this the "crossing" invariant.)

(When we say the event queue contains an event between $i$ and $j$, we mean that either there's
an exit event for some $alpha^k$ with $i < k < j$ or there's an intersection event for some $alpha^k$ and $alpha^ell$
with $i <= k < ell <= j$.)

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
+ The crossing invariant is maintained because the set of things to check (i.e. the set of line segments that $epsilon$-cross
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

The second property imposes a requirement on the allowable slopes for $alpha^1$ and $alpha^2$. With finite precision
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
are at least $epsilon$ apart and so we can compute intersections accurately enough.

#inexact[
in practice, there will be some numerical
errors in evaluating these definitions, but that's ok if we're careful about the error direction: if $beta(y)$ is just barely bigger than $alpha(y)$, we
can allow a false positive in the shuffle intersection test, and the numerical stability for the clear intersection
test will just be a little bit worse. On the other hand, we *insist* that for a clear intersection,
$beta(y)$ is truly at least $alpha(y)$ (and so we can give a lower bound on the intersection height that's larger than the current sweep height).
]

Now we're ready to talk about our replacement for Bentley-Ottmann's "just compare to the next segment" step. Imagine
we have an $epsilon$-ordered collection $(alpha^1, ..., alpha^m)$ and we want to see if $alpha^i$ intersects with anything
"before" it in the collection. We'll call this procedure an *intersection scan to the left*.
For each $j$ from $i - 1$ down to $1$, we test $alpha^j$ and $alpha^i$ for intersections.
- If there's a shuffle intersection, we add an intersection event to the event queue (with $y$-coordinate at the current scan-line)
  and continue.
- If there's a clear intersection, we add an intersection event to the event queue (with $y$-coordinate that lower-bounds the
  true intersection height; note that the definition of a clear intersection implies that we can find such a lower bound that's
  at least the current scan-line's height). Then we stop scanning.
- If we encounter a segment that's strictly to the left of $alpha^i$ from $y$ onwards, we stop scanning.
Just to compare once more to Bentley-Ottmann: with exact computations you only need to compare to one segment. Either
it intersects or it doesn't. With inexact computations, you keep scanning left until you either find something that
definitely intersects or definitely doesn't.

The *intersection scan to the right* is very similar to the intersection scan to the left: just increase $j$ instead of
decreasing it. An *intersection scan* combines the two (in either order).

#lemma[
Suppose $(alpha^1, ..., alpha^(i-1))$ satisfies the ordering and crossing invariants at $y$, and suppose that
$(alpha^1, ..., alpha^i)$ satisfies the ordering invariant at $y$. After running an intersection scan to the left,
it also satisfies the crossing invariant at $y$.

Similarly, suppose $(alpha^(i+1), ..., alpha^m)$ satisfies the ordering and crossing invariants at $y$, and suppose that
$(alpha^i, ..., alpha^m)$ satisfies the ordering invariant at $y$. After running an intersection scan to the right,
it also satisfies the crossing invariant at $y$.
]<lem-intersection-scan>

#proof[
We'll prove the first claim; the second is similar. Because the crossing invariant holds without $alpha^i$, we only
need to consider intersections involving $alpha^i$. So suppose that $j < i$ and $(alpha^j, alpha^i)$ $epsilon$-cross.
If we encountered $alpha^j$ when scanning for $alpha^i$'s intersections, we would have inserted an intersection event
and that intersection event would witness the crossing invariant. So let's assume that when scanning for $alpha^i$'s clear intersections,
we stopped the scan at $alpha^k$ for some $k > j$.

There are two reasons we might have stopped the clear intersection scan:
- if $alpha^k$ clearly intersects $alpha^i$, we inserted an intersection event at some $y$-coordinate that's less than or equal to the
  true intersection $y$-coordinate. Let $y_k$ be the $y$-coordinate of the intersection event that we inserted. There are two sub-cases:
  - if $alpha^j$ $epsilon$-crosses $alpha^i$ after $y_k$, then the intersection event we inserted witnesses
    the crossing invariant.
  - otherwise, $alpha^j$ $epsilon$-crosses $alpha^i$ before $y_k$, and therefore also before the true intersection between
    $alpha^k$ and $alpha^i$. Therefore, $alpha^j$ $epsilon$-crosses $alpha^k$ before $alpha^j$ $epsilon$-crosses $alpha^i$. By the
    crossing invariant for the old sweep-line, the queue contains some witnessing event for the $epsilon$-crossing of $alpha^j$ and $alpha^k$;
    and this event also witnesses the crossing invariant for the $epsilon$-crossing between $alpha^j$ and $alpha^i$.
- Otherwise, scanning terminated because $alpha^k$ doesn't meet $alpha^i$.
  - If $alpha^j$ $epsilon$-crosses $alpha^i$ after $alpha^k$ ends, the exit event witnesses the crossing invariant.
  - Otherwise, $alpha^j$ must $epsilon$-cross $alpha^k$ before it $epsilon$-crosses $alpha^i$. The crossing invariant
    for the old sweep-line guarantees the existence of an event witnessing the new sweep-line invariant.
]

#inexact[
when deciding when to stop scanning to the left, we can't exactly check whether a segment is strictly to the left of $alpha^i$.
We allow false negatives but not false positives; this might result in a little extra scanning, but it ensures that the proof
still works.
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

#inexact[
the inequalities $alpha^i (y) <= beta(y) <= alpha^(i+1) (y)$ need to be exact for the proof to work.
In the face of inexact computations, the problematic case is when $beta(y)$ is very close to (say) $alpha^i (y)$
and there is some $j < i$ with $alpha^j (y)$ very close to $alpha^i(y) + epsilon$. In this case we might
wrongly think that $beta(y) >= alpha^i (y)$, and by inserting $beta$ after $alpha^i (y)$ we break
the ordering invariant for $alpha^j$ and $beta$. This case can probably be handled by scanning left from $alpha^i$
to look for a problematic $alpha^j$; if we find one, ensure that $beta$ goes to the left of it. The correctness arguments
here require a bit more thought, but I think one important point is that we can't have a "problematic $alpha^j$" in *both*
directions, because if we did then those two problematic segments would be almost $2 epsilon$ out-of-order.
]

@lem-insert-preserving-order implies that we can insert a new segment while preserving the ordering invariant. By
@lem-intersection-scan, running an intersection scan restores the crossing invariant.
Thus, we can insert a new segment while preserving the sweep-line invariants.

== An "exit" event

When a segments exits the sweep-line, the ordering invariant clearly doesn't break.
Regarding the crossing invariant, it can only break because of $epsilon$-crossing pairs whose
crossing invariant was witnessed by the exit event that was just processed.
To restore the crossing invariant, we need to enqueue some new intersection events.

Let $(alpha^1, ..., alpha^m)$ be the sweep-line after removing the just-exited segment
which, we assume, used to live between $alpha^i$ and $alpha^(i+1)$. It is tempting to
intersection-scan $alpha^i$ to the right and $alpha^(i+1)$ to the left. By @lem-intersection-scan,
this ensures that the both $(alpha^1, ..., alpha^(i+1))$ and $(alpha^i, ..., alpha^m)$ satisfy
the crossing invariant. However, this does not imply that the whole sweep-line satisfies the
crossing invariant. For example, it is possible that $alpha^(i-1)$ sticks out $2/3 epsilon$
to the right of $alpha^i$ and $alpha^(i+2)$ sticks out $2/3 epsilon$ to the left of $alpha^(i+1)$,
and $alpha^(i-1)$ $epsilon$-crosses $alpha^(i+2)$ in violation of the crossing invariant.

To fix this problem, we will need a *strict intersection scan*, which is similar to the previous scan except
that we declare crossings at a threshold of $epsilon/2$ instead of $epsilon$, and
the stopping criterion is stricter. We'll describe only the leftward version,
starting at $alpha^i$. As before, we iterate $j$ from $i-1$ down to $1$. Unlike the non-strict version,
we will keep track of the soonest (i.e. smallest $y$-coordinate) clear intersection we've seen so far; call it $y^*$.
- If we encounter an $epsilon/2$-shuffle intersection, we add an intersection event, update $y^*$, and continue scanning.
- If we encounter as $epsilon/2$-clear intersection, we add an intersection event as before; we also update $y^*$ if appropriate.
  Then we check whether $alpha^j$ is at least $epsilon/2$ to the left of $alpha^j$ for all heights between $y$ and $y^*$.
  If so, we stop scanning.
- If we encounter a segment that's at least $epsilon/2$ to the left of $alpha^j$ for all heights between $y$ and $y^*$, we stop scanning.

The point of this strict intersection scan is that it imposes a crossing invariant with half the error (although only for $alpha^i$, and
only in one direction).
  
#lemma[
Suppose $(alpha^1, ..., alpha^(i-1))$ satisfies the ordering and crossing invariants at $y$, and suppose that
$(alpha^1, ..., alpha^i)$ satisfies the ordering invariant at $y$. After running a strict intersection scan to the left,
the following stronger crossing invariant holds: for every $j < i$, if $alpha^j$ $epsilon/2$-crosses $alpha^i$ then the
event queue contains an event between $j$ and $i$,
and at least one of these events occurs either before the $epsilon/2$-crossing height or at $y$.
]<lem-strict-intersection-scan>

#proof[
  Suppose $j < i$ and $alpha^j$ $epsilon/2$-crosses $alpha^i$. If the strict intersection scan included $j$, it would have
  inserted an intersection event for $alpha^j$ and $alpha^i$ (which would witness the crossing invariant),
  so let's suppose that the scan stopped at $k > j$ and recall the definition of $y^*$ (particularly the fact
  that we inserted an intersection event at height $y^*$). We consider two cases:
    - If $alpha^j$ $epsilon/2$-crosses $alpha^i$ after $y^*$ then the intersection event at $y^*$ witnesses the crossing invariant.
    - Otherwise, $alpha^j$ $epsilon/2$-crosses $alpha^i$ before $y^*$. Since $alpha^k$ is at least $epsilon/2$ less to the left
      of $alpha^i$ up to $y^*$, it follows that $alpha^j$ $epsilon$-crosses $alpha^k$ before it $epsilon/2$-crosses $alpha^i$.
      By the old crossing invariant, there is an event witnessing $alpha^j$ $epsilon$-crossing $alpha^k$; this same
      event witnesses $alpha^j$ $epsilon/2$-crossing $alpha^i$.
]

To finish handling the exit event, we run a strict intersection scan to the left of $alpha^i$ and a strict
intersection scan to the right of $alpha^(i+1)$. These two extra intersection scans ensure that without a witnessing
event in the queue, nothing "before" $alpha^i$ pokes out more than $epsilon/2$ to its right, and nothing "after"
$alpha^(i+1)$ pokes out more than $epsilon/2$ to its left. This eliminates the possibility of an unhandled
$epsilon$-crossing, and ensures that we maintain the crossing invariant.

== An "intersection" event

I don't think we've asserted this yet, but all intersection events in the queue always occur at a height where
the two crossing segments are within $epsilon$ of one another. Also, intersection events are only inserted
for $epsilon$-crossing segments, so it's always clear which order the segments should be in after the intersection.

Suppose our sweep-line is $(alpha^1, ..., alpha^m)$ and we've just encountered an intersection event for $alpha^i$ and $alpha^j$,
where $i < j$. First, we check whether $alpha^i$ and $alpha^j$ actually need to be swapped, as some other intersection event might
have already swapped them. If they're already in the correct order, we skip the re-ordering step and move on to the crossing invariant.
If $alpha^i$ and $alpha^j$
need to be re-ordered, we consider two possibilities: we can move $alpha^j$ before $alpha^i$ or we can move $alpha^i$ after $alpha^j$.
If $alpha^i(y) >= alpha^j(y)$ then either choice maintains the ordering invariant:

#lemma[
Suppose $(alpha^1, ..., alpha^m)$ satisfies the ordering invariant at $y$ and suppose that $i < j$ and $alpha^i (y) >= alpha^j (y)$.
Then $(alpha^1, ..., alpha^(i-1), alpha^(i+1), ..., alpha^j, alpha^i, alpha^(j+1), ... alpha^m)$ and
$(alpha^1, ..., alpha^(i-1), alpha^j, alpha^i, ..., alpha^(j-1), alpha^(j+1), ... alpha^m)$ both satisfy the ordering invariant
at $y$.
]<lem-reorder>

#proof[
  The two claims are essentially the same, so we will consider only the first one. When putting $alpha^i$ after $alpha^j$,
  the only pairs of segments whose order has changed are $(alpha^i, alpha^k)$ pairs for $i < k <= j$; hence, we only need
  to re-check the ordering invariant for those pairs. But for such $k$, the old ordering invariant implies
  that $alpha^k(y) - epsilon <= alpha^j (y)$, and since we assumed $alpha^j (y) <= alpha^i (y)$ it follows that
  $alpha^k (y) - epsilon <= alpha^i (y)$. Therefore, $alpha^i$ and $alpha^k$ satisfy the new ordering invariant.
]

It is possible, however that $alpha^i (y) < alpha^j (y)$. This is likely, even, because we tend to create intersection events
with a height that lower-bounds the actual intersection height. So in general we have a slightly more complex procedure:
choose $k$ with $i < k <= j$ to be the largest possible such that $alpha^k (y) <= alpha^i (y)$. Then move $alpha^i$ after $alpha^k$.
(This preserves the ordering invariant by @lem-reorder.) Finally, move $alpha^j$ before $alpha^i$'s new position. This maintains
the ordering invariant because the only pairs whose orders change were pairs of the form $(alpha^ell, alpha^j)$ for $k <= ell < j$
and the definition of $k$ ensures that $alpha^ell (y) >= alpha^i (y)$ (which is guaranteed to be at least $alpha^j (y) - epsilon$
by the fact that there was an intersection event).

=== Maintaining the crossing invariant

The final thing we need to do is explain how we maintain the crossing invariant. We'll do this in a slightly abstracted situation:
we have a sweep-line $(alpha^1, ..., alpha^m)$ that satisfies both invariants, and we move $alpha^i$ to after $alpha^j$ in such
a way that the ordering invariant is maintained. How do we maintain the crossing invariant? (The intersection-event processing
contains up to two of these "moves," so if we describe how to maintain the crossing invariant after one of these moves, we'll just
have to repeat that.)

In order to handle the crossing invariant of one swap, we treat it as an "exit" followed by an "entrance." That is,
to handle the removal of $alpha^i$ from its old location we run intersection scans on $alpha^(i-1)$ (strict to the left; non-strict
to the right) and $alpha^(i+1)$ (strict to the right; non-strict to the left). Then we run a (non-strict) intersection scan on $alpha^i$
in its new location.
