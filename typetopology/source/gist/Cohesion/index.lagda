The three safe indexes use Agda's native cohesion modalities. Claude
Fable 5.2 designed the parent index, Claude Opus 5.5 implemented it,
and GPT-6 Astra checked it. The two FlatSplit modules have separate
entry points because their crisp pattern matching uses --flat-split.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.Cohesion.index where

import gist.CohesiveApartness.index
import gist.Orbifolds.index
import gist.RealCohesion.index

\end{code}
