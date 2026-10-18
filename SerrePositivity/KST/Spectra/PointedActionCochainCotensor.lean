module

public import SerrePositivity.KST.Spectra.PointedActionCochainEquivalence
public import SerrePositivity.KST.Spectra.WeightedCochainsCotensor
public import SerrePositivity.KST.Spectra.PointedActionDiagrams

/-!
概要：点つき作用の余単体 cochain と内部 Hom の自然な交換同型。
方針：図式の段階で作った交換同型を作用の係数図式の後合成の比較へ合成する。
規約：円による loop に限らず任意の点つき源を許す。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の Ω 条件の構成。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.PointedActionCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：内部 Hom と作用の cochain の交換を係数に自然な同型として構成する。
方針：通常の図式での交換と、作用の係数図式の後合成との比較を合成する。
規約：end の巨大な表示を直接展開せず、構成済みの関手の同型を使う。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。cochain の loop 交換の関手的な形。 -/
def cotensorNatIso (A : PointedSimplicialSet.{u}) (G : Type u) [Group G] :
    functor G ⋙ (Functor.whiskeringRight SimplexCategory PointedSimplicialSet.{u}
        PointedSimplicialSet.{u}).obj (ihom A) ≅
      (ihom A).mapAction G ⋙ functor G :=
  Functor.isoWhiskerLeft (FreeActionFamily.pointedCoefficientsFunctor G)
      (WeightedCochains.cotensorNatIso A (GroupActionCochains.universalCoverWeight G)) ≪≫
    Functor.isoWhiskerRight (FreeActionFamily.pointedCoefficientsPostIso G (ihom A))
      (weightedCochainsFunctor (GroupActionCochains.universalCoverWeight G))

/-- 概要：内部 Hom と作用の余単体 cochain は自然に交換する。
方針：係数に自然な交換同型を指定した作用で評価する。
規約：両側は実際の点つき余単体図式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。loop と cochain の整合性。 -/
def cotensorIso {G : Type u} [Group G] (A : PointedSimplicialSet.{u})
    (B : Action PointedSimplicialSet.{u} G) :
    obj B ⋙ ihom A ≅ obj (((ihom A).mapAction G).obj B) :=
  (cotensorNatIso A G).app B

/-- 概要：cochain の cotensor 交換は係数の点つき同変射に自然。
方針：係数に自然な同型の自然性を取り出す。
規約：余単体の自然変換の厳密な等式。
使われ方：Goerss–Jardine VIII §2、HA §1.4.2。作用の射の Ω 列への移送。 -/
lemma cotensorIso_natural {G : Type u} [Group G] (A : PointedSimplicialSet.{u})
    {B C : Action PointedSimplicialSet.{u} G} (τ : B ⟶ C) :
    Functor.whiskerRight (map τ) (ihom A) ≫ (cotensorIso A C).hom =
      (cotensorIso A B).hom ≫ map (((ihom A).mapAction G).map τ) :=
  (cotensorNatIso A G).hom.naturality τ

end

end SerrePositivity.KST.Spectra.PointedActionCochains
