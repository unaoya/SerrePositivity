module

public import SerrePositivity.KST.Spectra.PointedHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanRelativeLifting

/-!
概要：Kan 複体間の anodyne 射の全基点 π_* 同型性。
方針：Kan な源への延長でレトラクションを作り、境界 pushout product で相対収縮する。
規約：ホーンの持ち上げ性だけを使い、HT-KQ を使わない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。Kan 置換単位の検証。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 複体への anodyne 包含には点つきレトラクションがある。
方針：Kan な源への恒等射を anodyne 射に沿って延長する。
規約：標的の Kan 性はこの段階では不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。置換の比較逆。 -/
theorem exists_pointedRetraction {A B : PointedSimplicialSet.{u}} [KanComplex A.right]
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i.right) :
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A := by
  have hA : J.rlp (terminal.from A.right) := (fibration_iff _).1 inferInstance
  obtain ⟨r, hr⟩ := KanHomotopyExtension.exists_extension i.right hi hA (𝟙 A.right)
  have hb : B.hom ≫ r = A.hom := by
    rw [← Under.w i, Category.assoc, hr, Category.comp_id]
  refine ⟨Under.homMk r hb, ?_⟩
  apply Under.UnderMorphism.ext
  exact hr

/-- 概要：anodyne 射のレトラクションとの合成を基点を固定して恒等射へ収縮する。
方針：包含上で定数のホモトピーを境界 pushout product に沿って延長する。
規約：標的は Kan、左逆は厳密な点つきレトラクション。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.1（Tag 00V4）。anodyne 射の π_* 保存。 -/
theorem exists_pointedRetractionHomotopy {A B : PointedSimplicialSet.{u}}
    [KanComplex B.right] (i : A ⟶ B) (hi : SSet.anodyneExtensions i.right)
    (r : B ⟶ A) (hr : i ≫ r = 𝟙 A) :
    ∃ H : SSet.Homotopy (r ≫ i).right (𝟙 B.right),
      B.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ B.hom := by
  have hir : i.right ≫ r.right = 𝟙 A.right := congrArg Under.Hom.right hr
  let H0 : SSet.Homotopy (i.right ≫ (r ≫ i).right) (i.right ≫ 𝟙 B.right) := {
    h := fst A.right (Δ[1] : SSet.{u}) ≫ i.right
    h₀ := by
      change SSet.ι₀ ≫ _ = i.right ≫ (r.right ≫ i.right)
      rw [← Category.assoc i.right r.right i.right, hir, Category.id_comp]
      rfl
    h₁ := by rfl
    rel := by ext n ⟨⟨x, hx⟩, t⟩; exact hx.elim }
  let pp := KanRelativeLifting.boundaryProduct i.right
  have ha : SSet.anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι' pp hi
  have hB : J.rlp (terminal.from B.right) := (fibration_iff _).1 inferInstance
  obtain ⟨H, hH⟩ := KanRelativeLifting.exists_extension i.right (ha _ hB)
    (r ≫ i).right (𝟙 B.right) H0
  refine ⟨H, ?_⟩
  rw [← Under.w i, comp_whiskerRight_assoc, hH]
  change A.hom ▷ (Δ[1] : SSet.{u}) ≫ (fst A.right _ ≫ i.right) = _
  rw [whiskerRight_fst_assoc, Under.w]
  rfl

/-- 概要：Kan な点つき対象間の anodyne 射は全自然数次数で全単射を誘導する。
方針：厳密な左逆と基点固定ホモトピーによる右逆を使う。
規約：零次数も含む。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Kan 置換比較の基点での検証。 -/
theorem pointedHomotopyMap_bijective_of_anodyne {A B : PointedSimplicialSet.{u}}
    [KanComplex A.right] [KanComplex B.right] (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i.right) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n i) := by
  obtain ⟨r, hr⟩ := exists_pointedRetraction i hi
  obtain ⟨H, hH⟩ := exists_pointedRetractionHomotopy i hi r hr
  let Hr := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedRelativeHomotopy (r ≫ i) (𝟙 B) H hH
  have hl : Function.LeftInverse (pointedHomotopyMap n r) (pointedHomotopyMap n i) := by
    intro a
    rw [← pointedHomotopyMap_comp, hr, pointedHomotopyMap_id]
  have hh : Function.RightInverse (pointedHomotopyMap n r) (pointedHomotopyMap n i) := by
    intro a
    rw [← pointedHomotopyMap_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_eq_of_basedHomotopy n _ _ Hr a).trans (pointedHomotopyMap_id B n a)
  exact ⟨hl.injective, hh.surjective⟩

/-- 概要：Kan 複体間の anodyne 射は全基点 π_* 同型。
方針：各基点で点つきレトラクションを構成し、基点の表示を移送する。
規約：L9 の零次数を含むホモトピー類の全単射性。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。置換射の検証。 -/
theorem kanPiIsomorphism_of_anodyne {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism i := by
  intro a n
  let Ap := PointedSimplicialSet.ofVertex A a
  let Bp := PointedSimplicialSet.ofVertex B (i.app _ a)
  let : KanComplex Ap.right := inferInstanceAs (KanComplex A)
  let : KanComplex Bp.right := inferInstanceAs (KanComplex B)
  let ip : Ap ⟶ Bp := Under.homMk i (by
    change SSet.const a ≫ i = SSet.const (i.app _ a)
    exact SSet.const_comp a i)
  have hb := pointedHomotopyMap_bijective_of_anodyne ip hi n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_bijective_congr n i
    (PointedSimplicialSet.basepoint_ofVertex A a)
    (PointedSimplicialSet.basepoint_ofVertex B (i.app _ a)) _ rfl hb

end

end SerrePositivity.KST.Spectra
