module

public import SerrePositivity.KST.Spectra.RawSpectrumHomPointInverse
public import SerrePositivity.KST.Spectra.RawSpectrumMappingPreNaturality

/-!
概要：d3 の Raw Hom の零単体を実 Kan 列射として回収し、二境界を照合する。
方針：既存の点つき単位パラメータ同値を用い、全段評価で前後合成を検査する。
規約：標的は任意の Kan 列。新しい転置・uncurry 実装を導入しない。
使われ方：比較族の相対充填から元の列射 r と BF 比較射 c を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- Raw Hom の零単体を既存の単位パラメータ同値で実列射へ戻す。 -/
def d3HomOfVertex (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (v : (space X Y) _⦋0⦌) :
    KanSequence.Hom X.toKanSequence Y :=
  homOfPoint X Y ((PointedSimplicialSet.unitVertexEquiv (pointedSpace X Y)).symm v)

/-- 零単体から回収した射の各段は、元の全 Hom の同じ段評価。 -/
lemma d3HomOfVertex_app (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (v : (space X Y) _⦋0⦌) (n : ℕ) :
    (d3HomOfVertex X Y v).app n =
      (pointedHomVertexEquiv _ _).symm ((evaluation X Y n).app _ v) := by
  change uncurry' (_ ≫ pointedEvaluation X Y n) = uncurry' _
  congr 1
  apply (PointedSimplicialSet.unitVertexEquiv _).injective
  rw [PointedSimplicialSet.unitVertexEquiv_naturality, Equiv.apply_symm_apply]
  exact ((PointedSimplicialSet.unitVertexEquiv _).apply_symm_apply _).symm

/-- 元の実列射を、同じ Raw Hom の終対象パラメータへ写す。 -/
def d3VertexMap (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Y) : 𝟙_ SSet.{u} ⟶ space X Y :=
  PointedSimplicialSet.unitUnderlyingHom (pointedSpace X Y) (homPoint X Y f)

/-- 元の実列射の頂点を各段に評価すると、元の段射を厳密回収する。 -/
lemma d3VertexMap_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f : KanSequence.Hom X.toKanSequence Y) (n : ℕ) :
    (evaluation X Y n).app _ ((space X Y).unitHomEquiv (d3VertexMap X Y f)) =
      pointedHomVertexEquiv _ _ (f.app n) := by
  change (pointedEvaluation X Y n).right.app _
    (PointedSimplicialSet.unitVertexEquiv _ (homPoint X Y f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, homPoint_evaluation]
  rfl

/-- 元の列射の終対象パラメータは BF 左因子による前合成を厳密に保つ。 -/
lemma d3VertexMap_pre {X L : OmegaSpectrum.{u}} (a : X ⟶ L) (Y : KanSequence.{u})
    (f : KanSequence.Hom L.toKanSequence Y) :
    d3VertexMap L Y f ≫ pre a Y =
      d3VertexMap X Y
        ((⟨a.app, a.comm⟩ : KanSequence.Hom X.toKanSequence L.toKanSequence).comp f) := by
  apply hom_ext X Y
  intro n
  apply (SSet.unitHomEquiv _).injective
  rw [Category.assoc, pre_evaluation, ← Category.assoc]
  simp only [OmegaSpectrum.unitHomEquiv_comp, d3VertexMap_evaluation]
  exact pointedHomVertexEquiv_pre (a.app n) (f.app n)

/-- 同じ終対象パラメータは元の列射による後合成も厳密に保つ。 -/
lemma d3VertexMap_post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (f : KanSequence.Hom X.toKanSequence Y) (q : KanSequence.Hom Y Z) :
    d3VertexMap X Y f ≫ post X q = d3VertexMap X Z (f.comp q) := by
  apply hom_ext X Z
  intro n
  apply (SSet.unitHomEquiv _).injective
  rw [Category.assoc, post_evaluation, ← Category.assoc]
  simp only [OmegaSpectrum.unitHomEquiv_comp, d3VertexMap_evaluation]
  exact pointedHomVertexEquiv_post (f.app n) (q.app n)

/-- 全 Raw Hom の前合成は、回収した元の列射の前合成そのもの。 -/
lemma d3HomOfVertex_pre {X L : OmegaSpectrum.{u}} (a : X ⟶ L) (Y : KanSequence.{u})
    (v : (space L Y) _⦋0⦌) (n : ℕ) :
    (d3HomOfVertex X Y ((pre a Y).app _ v)).app n =
      a.app n ≫ (d3HomOfVertex L Y v).app n := by
  dsimp only [OmegaSpectrum.toKanSequence]
  apply (pointedHomVertexEquiv (X.level n).space _).injective
  rw [d3HomOfVertex_app, d3HomOfVertex_app]
  simp only [Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (pre_evaluation a Y n) _) v
  change (evaluation X Y n).app _ ((pre a Y).app _ v) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (a.app n) (Y.level n).space).app _
    ((evaluation L Y n).app _ v) at h
  rw [h, ← pointedHomVertexEquiv_pre, Equiv.apply_symm_apply]

/-- 全 Raw Hom の後合成も、回収した元の列射の後合成そのもの。 -/
lemma d3HomOfVertex_post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (q : KanSequence.Hom Y Z) (v : (space X Y) _⦋0⦌) (n : ℕ) :
    (d3HomOfVertex X Z ((post X q).app _ v)).app n =
      (d3HomOfVertex X Y v).app n ≫ q.app n := by
  dsimp only [OmegaSpectrum.toKanSequence]
  apply (pointedHomVertexEquiv (X.level n).space _).injective
  rw [d3HomOfVertex_app, d3HomOfVertex_app]
  simp only [Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (post_evaluation X q n) _) v
  change (evaluation X Z n).app _ ((post X q).app _ v) =
    (PointedObject.basedHomMap _ (q.app n)).right.app _
    ((evaluation X Y n).app _ v) at h
  rw [h, ← pointedHomVertexEquiv_post, Equiv.apply_symm_apply]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
