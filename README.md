# Monsky's Theorem

Contributors (in alphabetical order): Dhyan Aranha, Pjotr Buys, Malvin Gattinger, Giacomo Grevink, Jan Hendriks, Thomas Koopman, Dion Leijnse, Thijs Maessen, Maris Ozols, Jonas van der Schaaf, Lenny Taelman

In this project we formalize the following theorem:

***Theorem (Monsky)*** : It is not possible to dissect a square into an odd number of triangles of equal area. 

We also formalize and prove the theorem that it is always possible to do this with an even number of triangles of equal area. 

***Theorem***: It is always possible to dissect a square into an even number of triangles of equal area.

(This was carried out by Pjotr Buys in [Monsky_even](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/Monsky_even.lean)

Below is a summary of our work with links to the relevant files in this repository. 

1) In [Appendix.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/Appendix.lean),
   it is shown that the real numbers admit a non-Archimedean valuation: v, with values in an orderd abelian group such that,
   v(1/2) > 1.

2) In [Rainbow_triangles.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/Rainbow_triangles.lean)
   using the valuation from 1) we construct a tri-coloring of the unit square S in R^2. We use this coloring to define the notion of
   ***rainbow triangle***: a triangle whose vertices consist of three different colors. We also prove various properties about this coloring.
   Two important ones are: i) Any line in S containes at most two colors, ii) The area of a rainbow triangle cannot be 0 and it cannot be 1/n
   for n odd.

3) The files [Segment_counting.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/segment_counting.lean) [Segment_triangle.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/segment_triangle.lean) and [square.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/square.lean) contain the proof of Monsky's theorem as well
  as the proof that even dissections always exist. This is by far the most technincal part of the work.  There are still a few sorrys which we hope to fill soon. For the latest developments in this file please check out the sperner branch. Here we would like to recognize
  the contributions of Pjotr Buys!

4) Finally in [Triangle_corollary.lean](https://github.com/dhyan-aranha/Monsky/blob/main/Monsky/Triangle_corollary.lean) we formalize the comparison
   between the area of a triangle in R^2 given by measure theory and the formula given in terms of the determinant.
