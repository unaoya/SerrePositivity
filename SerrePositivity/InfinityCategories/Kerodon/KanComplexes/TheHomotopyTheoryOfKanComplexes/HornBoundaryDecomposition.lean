module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.HornFaceBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
概要：標準単体の境界をホーンと欠けた面の pushout として表示する。
方針：部分複体の和と交わりを計算し、交わりを面の境界へ戻す。
規約：厳密な部分複体と通常の圏論的 pushout を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。相対三角形の境界の円の構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：ホーンは標準単体の境界に含まれる。
方針：ホーンを構成する各面の包含を境界へ送る。
規約：任意の欠けた面を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。境界の二部分による表示。 -/
theorem horn_le_simplexBoundary (n : ℕ) (i : Fin (n + 2)) :
    horn.{u} (n + 1) i ≤ boundary.{u} (n + 1) := by
  rw [horn_eq_iSup]
  exact iSup_le (fun j => face_singleton_compl_le_boundary j.val)

/-- 概要：ホーンとその欠けた面を合わせると標準単体の境界になる。
方針：全ての面を欠けた面とそれ以外に分ける。
規約：部分複体の厳密な等式。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。境界の pushout の構成。 -/
theorem horn_sup_missing_face (n : ℕ) (i : Fin (n + 2)) :
    horn.{u} (n + 1) i ⊔ stdSimplex.face {i}ᶜ = boundary.{u} (n + 1) := by
  apply le_antisymm
  · exact sup_le (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary n i) (face_singleton_compl_le_boundary i)
  · rw [boundary_eq_iSup]
    apply iSup_le
    intro j
    by_cases h : j = i
    · subst j
      exact le_sup_right
    · exact (face_le_horn j i h).trans le_sup_left

/-- 概要：ホーンと欠けた面の共通部分。
方針：同じ標準単体の部分複体の交わりを取る。
規約：境界の pushout の左上の対象。
使われ方：Goerss–Jardine I §7。面の境界とホーンの共通部分の比較。 -/
abbrev hornFaceOverlap (n : ℕ) (i : Fin (n + 2)) :
    (Δ[n + 1] : SSet.{u}).Subcomplex := horn.{u} (n + 1) i ⊓ stdSimplex.face {i}ᶜ

/-- 概要：境界はホーンと欠けた面を共通部分で貼り合わせた pushout。
方針：部分複体の双カルテジアン正方形を単体集合へ送る。
規約：射は全て部分複体の実際の包含。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。相対三角形の対角辺の包含の検査。 -/
theorem hornBoundaryPushout (n : ℕ) (i : Fin (n + 2)) :
    IsPushout
      (Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i ≤ horn (n + 1) i from inf_le_left))
      (Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i ≤ stdSimplex.face {i}ᶜ from inf_le_right))
      (Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary n i))
      (Subcomplex.homOfLE (face_singleton_compl_le_boundary i)) :=
  Subcomplex.BicartSq.isPushout { sup_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_sup_missing_face n i, inf_eq := rfl }

/-- 概要：共通部分を標準面の境界へ戻す射。
方針：面の標準単体との同型の逆を使い、ホーンの逆像の計算で境界への因子分解を得る。
規約：共通部分からの実際の単体的な射。
使われ方：Goerss–Jardine I §7。円の辺とホーンの貼り合わせの両立。 -/
def hornFaceOverlapToBoundary (n : ℕ) (i : Fin (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i : SSet.{u}) ⟶ (boundary.{u} n : SSet.{u}) := by
  let q : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) :=
    Subcomplex.homOfLE inf_le_right ≫ (stdSimplex.faceSingletonComplIso i).inv
  have he : q ≫ stdSimplex.δ i = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i).ι := by
    dsimp only [q]
    rw [Category.assoc, ← stdSimplex.faceSingletonComplIso_hom_ι,
      Iso.inv_hom_id_assoc]
    rfl
  refine Subcomplex.lift q ?_
  intro m v hv
  obtain ⟨s, rfl⟩ := hv
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.preimage_horn_face n i]
  change (stdSimplex.δ i).app m (q.app m s) ∈ (horn.{u} (n + 1) i).obj m
  have hs := ConcreteCategory.congr_hom
    (congrArg (fun f : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i : SSet.{u}) ⟶ (Δ[n + 1] : SSet.{u}) =>
      f.app m) he) s
  change (stdSimplex.δ i).app m (q.app m s) = s.val at hs
  rw [hs]
  exact s.property.1

/-- 概要：共通部分を境界へ戻して標準面へ含めると元の面の同型の逆に一致する。
方針：部分複体への lift の標準射での式を使う。
規約：射の厳密な等式。
使われ方：Goerss–Jardine I §7。境界上の写像をホーンと面から貼り合わせる。 -/
@[reassoc (attr := simp)]
theorem hornFaceOverlapToBoundary_ι (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary.{u} n i ≫ (boundary.{u} n).ι =
      Subcomplex.homOfLE (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap.{u} n i ≤ stdSimplex.face {i}ᶜ from inf_le_right) ≫
        (stdSimplex.faceSingletonComplIso i).inv := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary]
  exact Subcomplex.lift_ι _ _

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornBoundaryPushout := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornBoundaryPushout

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlap := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlap

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary_ι := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary_ι_assoc

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.horn_le_simplexBoundary := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_le_simplexBoundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.horn_sup_missing_face := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.horn_sup_missing_face

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.hornFaceOverlapToBoundary._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.hornFaceOverlapToBoundary._proof_3
