Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The interface Sharp-Modality of gist.RealCohesion.Sharp, instantiated
with the native ♯ of Agda 2.9.0 (gist.CohesiveApartness.Sharp).

gist.RealCohesion.Sharp takes ♯, its unit, recursion into types of
the form ♯ B and crisp induction as the fields of a record, because
Agda 2.8 has no ♯. With the native ♯ the four fields are definitions.
So the results that take the record as a parameter, those of
gist.RealCohesion.AxiomTObstruction, hold with no assumption about ♯
once they are instantiated with native-sharp, as in
gist.RealCohesion.Theorems. Codiscreteness relative to the native ♯
is is-codiscrete native-sharp, in the notation of
gist.RealCohesion.Sharp.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.NativeSharp where

open import MLTT.Spartan
open import gist.CohesiveApartness.Sharp
open import gist.RealCohesion.Sharp using (Sharp-Modality)

native-sharp : Sharp-Modality
native-sharp = record
                { ♯               = λ A → ♯ A
                 ; unit-sharp      = unit-sharp
                 ; rec-sharp       = rec-sharp
                 ; crisp-ind-sharp = crisp-ind-sharp
                 }

\end{code}
