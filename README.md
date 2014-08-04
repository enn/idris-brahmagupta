idris-brahmagupta
=================

multiply out brackets


This requires 

   %case data Ordering = LT | EQ | GT

as a change to line 60 of libs/prelude/Prelude/Classes.idr

because I need to use cases analysis on Ordering in a proof.
