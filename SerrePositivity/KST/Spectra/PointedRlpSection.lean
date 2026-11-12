module

public import SerrePositivity.KST.Spectra.PointedPrecompositionNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-!
概要：全単射 RLP を持つ点つき射の切断と、切断の自然性の垂直な実区間。
方針：基点包含を固定して切断を持ち上げ、同じ射影の二辺を相対充填する。
規約：Kan 性や ModelCategory を仮定しない。使われ方：普遍区間の全標的への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 全単射 RLP を持つ点つき射には、基点を保つ実際の切断がある。 -/
lemma exists_pointed_section {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) :
    ∃ s : B ⟶ E, s ≫ p = 𝟙 B := by
  let baseMono : Mono B.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono B
  let liftBase : HasLiftingProperty B.hom p.right := hp _ baseMono
  let sq : CommSq E.hom B.hom p.right (𝟙 B.right) := ⟨by rw [Under.w p, Category.comp_id]⟩
  exact ⟨Under.homMk sq.lift sq.fac_left, Under.UnderMorphism.ext sq.fac_right⟩

/-- 全族を同じ射影へ厳密に持ち上げる、基点固定の切断。 -/
def sectionOfRlp {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) : B ⟶ E :=
  (exists_pointed_section p hp).choose

/-- 選んだ切断の射影は恒等族に厳密一致する。 -/
lemma sectionOfRlp_condition {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) :
    sectionOfRlp p hp ≫ p = 𝟙 B := (exists_pointed_section p hp).choose_spec

/-- 可換四角形の二つの切断像は、同じ射影を固定する基点固定実区間で結べる。 -/
lemma section_naturality_nonempty {E B E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (p' : E' ⟶ B') (hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p'.right)
    (e : E ⟶ E') (b : B ⟶ B') (h : e ≫ p' = p ≫ b) :
    Nonempty (VerticalPath p' (sectionOfRlp p hp ≫ e) (b ≫ sectionOfRlp p' hp')) := by
  let f := sectionOfRlp p hp ≫ e
  let g := b ≫ sectionOfRlp p' hp'
  have hf : f ≫ p' = g ≫ p' := by
    change (sectionOfRlp p hp ≫ e) ≫ p' = (b ≫ sectionOfRlp p' hp') ≫ p'
    calc
      _ = sectionOfRlp p hp ≫ (p ≫ b) := by rw [Category.assoc, h]
      _ = b := by rw [← Category.assoc, sectionOfRlp_condition, Category.id_comp]
      _ = _ := by rw [Category.assoc, sectionOfRlp_condition, Category.comp_id]
  let baseMono : Mono B.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono B
  have hb : B.hom ≫ f.right = B.hom ≫ g.right := by rw [Under.w f, Under.w g]
  obtain ⟨H, hP, hB⟩ := MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy
    p'.right hp' B.hom f.right g.right (congrArg Under.Hom.right hf) hb
  have hbase : B.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E'.hom := by
    rw [hB, Under.w f]
    rfl
  exact ⟨VerticalPath.ofHomotopy H hbase hP⟩

/-- 二つの切断像を結び、同じ射影全体を固定する実際の自然性区間。 -/
def sectionNaturalityInterval {E B E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (p' : E' ⟶ B') (hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p'.right)
    (e : E ⟶ E') (b : B ⟶ B') (h : e ≫ p' = p ≫ b) :
    VerticalPath p' (sectionOfRlp p hp ≫ e) (b ≫ sectionOfRlp p' hp') :=
  Classical.choice (section_naturality_nonempty p hp p' hp' e b h)

/-- 切断の自然性区間の射影は、元の同じ基底射で辺全体が一定。 -/
lemma sectionNaturalityInterval_over {E B E' B' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (p' : E' ⟶ B') (hp' : (MorphismProperty.monomorphisms SSet.{u}).rlp p'.right)
    (e : E ⟶ E') (b : B ⟶ B') (h : e ≫ p' = p ≫ b) :
    (sectionNaturalityInterval p hp p' hp' e b h).path ≫
        (PointedObject.basedHomMap B p').right = SSet.const (familyVertex b) := by
  have hf : (sectionOfRlp p hp ≫ e) ≫ p' = b := by
    rw [Category.assoc, h, ← Category.assoc, sectionOfRlp_condition, Category.id_comp]
  exact (sectionNaturalityInterval p hp p' hp' e b h).over.trans
    (congrArg (fun f => SSet.const (familyVertex f)) hf)

end SerrePositivity.KST.Spectra.PointedMapping
