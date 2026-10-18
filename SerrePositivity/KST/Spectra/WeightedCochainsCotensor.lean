module

public import SerrePositivity.KST.Spectra.WeightedCochains
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensorWeight

/-!
概要：単体的な重みの余単体 cochain と内部 Hom の係数に自然な交換同型。
方針：重みと係数の二つの自然性を、図式の関手圏の自然同型として束ねる。
規約：作用図式への適用前に通常の図式の段階で比較を構成する。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の loop 交換の共通部分。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet Opposite

namespace SerrePositivity.KST.Spectra.WeightedCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I]

/-- 概要：単体的な重みの cochain と内部 Hom の交換同型。
方針：各次数の end の交換を重みへの自然性で束ねる。
規約：係数は任意の点つき図式。
使われ方：Goerss–Jardine VIII §2。cochain の Ω 列の構造の入力。 -/
def cotensorIso (A : PointedSimplicialSet.{u}) (W : SimplicialObject (I ⥤ SSet.{u}))
    (D : I ⥤ PointedSimplicialSet.{u}) :
    weightedCochains W D ⋙ ihom A ≅ weightedCochains W (D ⋙ ihom A) :=
  NatIso.ofComponents
    (fun n ↦ PointedWeightedEnd.cotensorIso A (W.obj (op n)) D)
    (fun f ↦ PointedWeightedEnd.cotensorIso_preMap A (W.map f.op) D)

/-- 概要：cochain と内部 Hom の交換を係数の図式に自然な同型へ束ねる。
方針：各次数の交換の係数への自然性を適用する。
規約：自然性は関手圏の中で厳密な等式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。作用の cochain へ交換を移すための比較。 -/
def cotensorNatIso (A : PointedSimplicialSet.{u}) (W : SimplicialObject (I ⥤ SSet.{u})) :
    weightedCochainsFunctor W ⋙
        (Functor.whiskeringRight SimplexCategory PointedSimplicialSet.{u}
          PointedSimplicialSet.{u}).obj (ihom A) ≅
      (Functor.whiskeringRight I PointedSimplicialSet.{u} PointedSimplicialSet.{u}).obj (ihom A) ⋙
        weightedCochainsFunctor W :=
  NatIso.ofComponents (fun D ↦ cotensorIso A W D) (fun {D E} τ ↦ by
    apply NatTrans.ext
    funext n
    exact PointedWeightedEnd.cotensorIso_natural A (W.obj (op n)) τ)

end

end SerrePositivity.KST.Spectra.WeightedCochains
