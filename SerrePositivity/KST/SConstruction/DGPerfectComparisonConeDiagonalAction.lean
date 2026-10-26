module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingComparisonZero

/-!
概要：元二実像小基底上の厳密比較について、実 cone 作用の第三成分零を回収する。
方針：同じ元比較の恒等 Hom gluing 関手へ全 cochain 零性を特殊化する。
規約：元商と二関手の全 Hom を保持。使われ方：逆回転後の合成比較の全自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))
  (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)
local notation "T" => DGPerfectComparisonBase R E F G
local notation "I" => DGFunctor.id (T)
local notation "H" => dgPerfectComparisonHomGluingFunctor R E F G τ

/-- 概要：同じ二実像小基底内の比較族は、実 cone の第三 cochain を消す。
方針：同じ元比較射と同じ全 Hom 自然性を恒等 gluing の零性へ渡す。
規約：第三成分零を追加仮定にしない。使われ方：実逆回転比較の始域上の簡約。 -/
lemma dgPerfectComparisonHomGluingFunctor_conePrimitive_zero (x y : P) :
    (Cochain.ofHom ((H).map x y)).comp
      (dgHomGluingConePrimitive R (T) (T) (T) (I) (I) ((H).obj x) ((H).obj y))
      (zero_add (-1)) = 0 :=
  dgIdentityHomGluingFunctor_conePrimitive_zero R (T)
    (dgPerfectComparisonFirst R E F G) (dgPerfectComparisonSecond R E F G)
    (dgPerfectComparisonMap R E F G τ) (dgPerfectComparisonMap_hom_naturality R E F G τ) x y
end SerrePositivity.KST.SConstruction
