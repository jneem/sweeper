#import "@preview/ctheorems:1.1.0": *

#show: thmrules
#let lemma = thmbox("lemma", "Lemma")

We'll be talking about sweep line algorithms, where the sweep line is horizontal and increasing in $y$.
Therefore, every line segment "starts" at the coordinate with smaller $y$ and "ends" at the coordinate
with larger $y$ (we'll assume for now that there are no horizontal segments). We'll parametrize each
line segment as a function of $y$. So if $alpha: [y_0 (alpha), y_1 (alpha)] arrow bb(R)$ is a line segment
then $alpha(y)$ is the $x$ coordinate at $y$-coordinate $y in [y_0 (alpha), y_1 (alpha)]$

We'll only deal with closed paths for now, so there are three kinds of points that can be hit by the sweep
line: points that have a locally minimal $y$ coordinate on their path, points that have a locally maximal $y$
coordinate on their path, and points that have neither. A picture would be nice here...

Define a relation $lt.curly_(y,epsilon)$ on line segments whose domain contains $y$, where
$alpha lt.curly_(y,epsilon) beta$ if $alpha(y) + epsilon < beta(y)$.
Despite our choice of symbol, this is not necessarily transitive.

Define a relation $tilde.op_(y,epsilon)$ on line segments whose domain contains $y$, where
$alpha tilde.op_(y, epsilon) beta$ if
the two line segments are within $epsilon$ of one another from $y$ up until the first time when one of them
ends. That is,
$alpha tilde.op_(y, epsilon) beta$ if $|alpha(y') - beta(y')| <= epsilon$ for all $y' in [y, "min"(y_1 (alpha), y_1 (beta))]$.

== The insertion philosophy

We're starting with continuous closed paths, and we want to finish with
continuous closed paths. We'll achieve this by keeping track of the paths as
we sweep the line (as opposed to the classical Bentley-Ottmann algorithm, which
just treats all line segments individually). The algorithm is designed to be
careful about the topology. This is a little tricky because for a sweep line
it can be numerically hard to check how the segments are ordered. So we don't
claim to find all the intersection points between all the segments, but we do
try to ensure some "large-scale" correctness of the intersections: if you
consider two sweep-lines and two continuous path going between them that are
sufficiently far from one another at the sweep-lines, then the number of intersections
we find between those paths will have the correct parity.

In order to track the continuity of the paths, each "enter" and "leave" event
will keep track of the line segments before *and* after the vertex.
We *never split segments*. This is handy because splitting segments means perturbing
them, which can mess up our invariants. Instead, we record intersections like "segment $alpha$
intersected segment $beta$ at height $y$; before this, $alpha$ was to the right of $beta$".
The approximate $x$ coordinate of the intersection can be obtained in a later pass. (And probably
that pass can also perturb the line segments so that the intersections become exact.)

== The sweep-line invariants

We will maintain a sorted-ish "sweep-line" data structure $(alpha^1, ..., alpha^m)$, which at height $y$ has the following invariants:
+ all line segments' domain contains $y$
+ if $alpha^i lt.curly_(y,epsilon) alpha^j$ then $i < j$
+ for every $i < j$, if $alpha^i$ and $alpha^j$ $epsilon$-cross after $y$,
  then the event queue contains an event for some $j' in (i, j)$,
  and at least one of these events occurs
  at a $y$ coordinate where nothing has yet $epsilon$-crossed $alpha^i$.

(We say that $alpha^j$ $epsilon$-crosses $alpha^i$ at $y'$ if $j < i$ and $alpha^j gt.curly_(y',epsilon) alpha^i$
or $i < j$ and $alpha^i gt.curly_(y',epsilon) alpha^j$.)

== Sweeping the sweep line

The first observation is that the sweep line invariants are maintained as we increase $y$ up
to the next event:
+ There is an event whenever $y$ leaves the domain of a segment, so $y$ remains in all domains until the next event.
+ In order for this invariant to fail, two line segments must $epsilon$-cross one another. The third invariant
  guarantees that there's an event before this happens.
+ This invariant is maintained because the set of things to check (i.e. the set of line segments that cross $epsilon$-cross
  one another after $y$) only shrinks as $y$ increases.

== An "exit-enter" event

An "exit-enter" event is the kind of event that happens when we encounter the end of a line segment
and the beginning of the next, and the vertex where it happens doesn't have a locally extremal $y$ coordinate.
When we encounter such an event, we remove the finished segment from the sweep-line and insert
the next one. We try to insert the new segment at the same position as the old one; let's call this position
$i$ and so the new segment is $alpha^i$. Let's call the removed segment $alpha^i_"old"$.

First, note that the first sweep-line invariant is trivially satisfied. The
second sweep-line invariant is satisfied because it was satisfied before
removing $alpha^i_"old"$ and $alpha^i(y) = alpha^i_"old" (y)$. But the third
sweep-line invariant might be broken and so we need to fix it. There are up
to two things we'll do to fix the invariant: we might "move" the starting $x$
coordinate of $alpha^i$ by inserting a small horizontal segment (and recording
its intersections with whatever segments it crosses). And we might insert an
intersection event into the event queue.

First, we compare $alpha^i$ to $alpha^j$ for $j < i$. 
We'll start at $j = i-1$ and keep going down
until we decide to stop. Whenever we encounter $alpha^j$ that $epsilon/2$ crosses $alpha^i$
(which, recalling that $j < i$ means that $alpha^j$ eventually goes $epsilon/2$ above $alpha^i$),
we check whether the crossing is $epsilon/2$-robust. If it isn't,
we move $alpha^i$ below $alpha^j$ in the sweep line and record the
fact that $alpha^j$ intersected all the $alpha^k$ for $j <= k < i - 1$. If the crossing is $epsilon/2$-robust,
we find the $y$-coordinate of the
intersection and insert an intersection event; then we stop scanning $j$ downwards.
Finally, we stop scanning $j$ downwards if we encounter some $alpha^j$ that starts below $alpha^i (y) - epsilon$.
Note that the new segment (which used to be called $alpha^i$) is not necessarily at index $i$ anymore. Instead
it is at some index $i_0 <= i$.

Before moving onto the upward scan, note that in moving the new segment from index $i$ to index $i_0$ we haven't broken the second sweep-line invariant:
we only moved the new segment below $alpha^j$ if there was an $epsilon/2$-crossing (meaning $alpha^j$ ended up $epsilon/2$ above)
that wasn't $epsilon/2$-robust (implying that $alpha^j$ started above the new segment). Since $k > j$ implies that
$alpha^k (y) > alpha^j (y) - epsilon >= alpha^i (y) - epsilon$, all of the $alpha^k$ that got moved above $alpha^i$ were allowed there.

When scanning $j$ upwards, we start with $j = i + 1$ (i.e. the index above the place where we originally inserted
the new segment), and we'll compare the segments $alpha^j$ with the new segment $alpha^(i_0)$.
Again, we look for $epsilon/2$-crossings. If they are not $epsilon/2$-robust, we move $alpha^(i+1)...alpha^j$ below $alpha^(i_0)$ and
record intersection events for all the intervening segments. If the crossing is $epsilon/2$-robust, we insert an intersection event and stop.
Again, we also stop scanning if we encounter some $alpha^j$ that starts above $alpha^(i_0) (y) + epsilon$.

The upwards scan preserved the second invariant for the same reason as the downwards scan; we just have to check whether the combination
of the two scans inserted enough intersection events to make the third invariant hold. Details TBD, but the outline is
that we only need to check whether the scan terminated too early. Say our downwards scan terminated at $j$ but there
was some $j' < j$ that intersects the new segment. If we terminated because $j$ intersects the new segment, then $j'$ must intersect $j$
before it intersects the new one, and so we can apply the third invariant for $j'$ and $j$ (because it held before we processed
the new segment) to see that there is an intersection event between $j'$ and $j$ (and therefore between $j'$ and $i$).
On the other hand, if we terminated because $j$ doesn't intersect the new segment then $j$ must have an end event before
the intersection of $j'$ and $i$; this event witnesses the third invariant.

== An "enter-enter" event

This adds two new segments, and we process it much like the "exit-enter" except that
- we start by searching for a good insertion point (because it isn't topologically predetermined for us)
- we decide in advance which of our two new segments is "above"
- when scanning down we consider crossings only for the lower segment, and when scanning up we consider crossing only for the upper segment
- we allow the two new segments to get "separated" in the sweep line (anything that gets put in between them will have an intersection recorded)

== An "exit-exit" event

On an exit-exit event
- we mark intersections for all segments that were between the two removed segments on the sweep line
- we test crossings for the segment that was right of the two removed segments

== An intersection event

We record an intersection, swap the order of the intersecting segments in the sweep line, and then check them both for more crossings.
