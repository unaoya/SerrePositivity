module
public import SerrePositivity.KST.SConstruction.DiagonalConnected
public import SerrePositivity.KST.SConstruction.KSpace
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-! # Kan 置換した S• 実現の連結性
概要：対角実現の連結性は anodyne な Kan 置換の単位で保たれる。
方針：既存の実際の π₀ の全単射を用い、連結成分と非空性を移す。
規約：BGT §7。anodyne 局所化自体を K の定義には使わない。
使われ方：K 空間の delooping の入力となる連結 Kan 実現。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：anodyne 射は実際の連結成分で全単射を誘導する。
方針：既存の π₀ 関手による anodyne 射の可逆化を Type の全単射へ戻す。
規約：両端の Kan 性は不要。使われ方：対角の Kan 置換の連結性。 -/
lemma mapPiZero_bijective_of_anodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : anodyneExtensions f) : Function.Bijective (SSet.mapπ₀ f) := by
  have h := SerrePositivity.SimplicialModel.PiZeroLocalization.inverts_anodyne f hf
  exact (CategoryTheory.isIso_iff_bijective (SSet.π₀Functor.map f)).1 h

/-- 概要：連結な単体集合の anodyne 延長は連結。
方針：連結成分の全射で前連結性を移し、元の頂点の像で非空性を得る。
規約：両端の Kan 性は不要。使われ方：実現の連結性の Kan 模型への移送。 -/
lemma isConnected_of_anodyne {A B : SSet.{u}} [SSet.IsConnected A]
    (f : A ⟶ B) (hf : anodyneExtensions f) : SSet.IsConnected B := by
  have hs := (mapPiZero_bijective_of_anodyne f hf).2
  letI : SSet.IsPreconnected B := ⟨by
    intro a b
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    exact congrArg (SSet.mapπ₀ f) (Subsingleton.elim x y)⟩
  exact ⟨SSet.nonempty_of_hom f⟩

/-- 概要：S• 実現の Kan 置換の単位は連結成分の全単射を誘導する。
方針：構成済みの単位の anodyne 性を使う。
規約：対角自体の Kan 性は仮定しない。使われ方：二つの実現模型の π₀ の照合。 -/
lemma sRealizationToKan_piZero_bijective (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    Function.Bijective (SSet.mapπ₀ (sRealizationToKan C).right) :=
  mapPiZero_bijective_of_anodyne _ (sRealizationToKan_anodyne C)

/-- 概要：Kan 置換した単体的 core の実現は連結。
方針：対角実現の連結性を anodyne な単位に沿って移す。
規約：零対象を持つ quasicategory に適用でき、安定性は不要。
使われ方：K(C) の連結な delooping 空間。 -/
instance kanSRealization_isConnected (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    SSet.IsConnected (kanSRealization C).right := by
  letI : SSet.IsConnected (pointedSRealization C).right := diagonalCoreSConstruction_isConnected C
  exact isConnected_of_anodyne (sRealizationToKan C).right (sRealizationToKan_anodyne C)

end SerrePositivity.KST.SConstruction
