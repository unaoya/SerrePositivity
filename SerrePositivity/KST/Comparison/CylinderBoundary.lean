module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.DoubleMappingCylinder
public import SerrePositivity.KST.Comparison.IntervalBoundaryFamily

/-!
# 円筒の端点の余積と境界包含

概要：円筒の二つの端点の余積を C⊗∂Δ[1] と同定する。
方針：零次標準単体との積の同型と、区間の境界の余積の普遍性を使う。
規約：Segal 1974 Lemma 1.7 の二重写像円筒の貼り付けの脚。
使われ方：貼り付けの脚の単射性と局所化不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial

/--
概要：零次標準単体との直積を元の対象に同定する。
方針：第一射影と、零次標準単体への唯一の射による積への射を使う。
規約：Mathlib の tensor unit と Δ[0] の間の同一視を仮定しない。
使われ方：二つの端点の余積の境界への移送。
-/
def simplexZeroTensorIso (C : SSet.{u}) : C ⊗ (Δ[0] : SSet.{u}) ≅ C where
  hom := fst C _
  inv := lift (𝟙 C) (SSet.stdSimplex.isTerminalObj₀.from C)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by simp

/--
概要：二つの C の余積は C と区間の境界の直積に同型である。
方針：各 C を C⊗Δ[0] に移し、境界の二頂点の余積の普遍性を使う。
規約：第一成分が零端点、第二成分が一端点。
使われ方：円筒の貼り付けの脚を境界包含へ移す。
-/
def cylinderBoundaryIso (C : SSet.{u}) : C ⨿ C ≅ C ⊗ (SSet.boundary.{u} 1) :=
  coprod.mapIso (simplexZeroTensorIso C).symm (simplexZeroTensorIso C).symm ≪≫
    (coprodIsCoprod (C ⊗ (Δ[0] : SSet.{u})) (C ⊗ (Δ[0] : SSet.{u}))).coconePointUniqueUpToIso
      (intervalBoundaryTensorIsColimit C)

/--
概要：境界への同型の第一成分は、零次標準単体との積への同型と零端点の合成である。
方針：余積の写像と余極限の比較同型の合成則を使う。
規約：boundary.ι 1 が区間の零頂点。
使われ方：端点の貼り付けとの一致。
-/
@[reassoc] theorem cylinderBoundaryIso_inl (C : SSet.{u}) :
    coprod.inl ≫ (cylinderBoundaryIso C).hom =
      (simplexZeroTensorIso C).inv ≫ C ◁ SSet.boundary.ι.{u} (1 : Fin 2) := by
  change coprod.inl ≫ coprod.map (simplexZeroTensorIso C).inv (simplexZeroTensorIso C).inv ≫ _ = _
  rw [coprod.inl_map_assoc]
  exact congrArg (fun q => (simplexZeroTensorIso C).inv ≫ q)
    ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
      (intervalBoundaryTensorIsColimit C) ⟨WalkingPair.left⟩)

/--
概要：境界への同型の第二成分は、零次標準単体との積への同型と一端点の合成である。
方針：余積の写像と余極限の比較同型の合成則を使う。
規約：boundary.ι 0 が区間の一頂点。
使われ方：端点の貼り付けとの一致。
-/
@[reassoc] theorem cylinderBoundaryIso_inr (C : SSet.{u}) :
    coprod.inr ≫ (cylinderBoundaryIso C).hom =
      (simplexZeroTensorIso C).inv ≫ C ◁ SSet.boundary.ι.{u} (0 : Fin 2) := by
  change coprod.inr ≫ coprod.map (simplexZeroTensorIso C).inv (simplexZeroTensorIso C).inv ≫ _ = _
  rw [coprod.inr_map_assoc]
  exact congrArg (fun q => (simplexZeroTensorIso C).inv ≫ q)
    ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
      (intervalBoundaryTensorIsColimit C) ⟨WalkingPair.right⟩)

/--
概要：零次標準単体との積への同型に零頂点の包含を合成すると円筒の零端点となる。
方針：各次数の直積の二成分で確認する。
規約：δ¹ が零頂点を表す。
使われ方：二つの端点の貼り付けの脚の同定。
-/
theorem simplexZeroTensorIso_zero (C : SSet.{u}) :
    (simplexZeroTensorIso C).inv ≫ C ◁ SSet.stdSimplex.δ (1 : Fin 2) = SSet.ι₀ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    rfl

/--
概要：零次標準単体との積への同型に一頂点の包含を合成すると円筒の一端点となる。
方針：各次数の直積の二成分で確認する。
規約：δ⁰ が一頂点を表す。
使われ方：二つの端点の貼り付けの脚の同定。
-/
theorem simplexZeroTensorIso_one (C : SSet.{u}) :
    (simplexZeroTensorIso C).inv ≫ C ◁ SSet.stdSimplex.δ (0 : Fin 2) = SSet.ι₁ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    rfl

/--
概要：円筒の端点の余積からの射は境界包含との積に同型を前合成したものである。
方針：余積の二成分で、境界の頂点の包含との合成を計算する。
規約：Segal Lemma 1.7 の貼り付けの脚を標準的な境界包含へ移す。
使われ方：貼り付けの脚の単射性。
-/
theorem cylinderEndpoints_factor (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C = (cylinderBoundaryIso C).hom ≫ C ◁ (SSet.boundary.{u} 1).ι := by
  apply coprod.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inl_desc, cylinderBoundaryIso_inl_assoc,
      ← whiskerLeft_comp, SSet.boundary.ι_ι, simplexZeroTensorIso_zero]
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints, coprod.inr_desc, cylinderBoundaryIso_inr_assoc,
      ← whiskerLeft_comp, SSet.boundary.ι_ι, simplexZeroTensorIso_one]

/--
概要：円筒の両端点の余積から円筒への射は単射である。
方針：境界包含との直積と同型の合成として表す。
規約：二重写像円筒を単射に沿った pushout として扱う。
使われ方：貼り合わせの局所化不変性。
-/
instance cylinderEndpoints_mono (C : SSet.{u}) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.cylinderEndpoints C) := by
  have : Mono (C ◁ (SSet.boundary.{u} 1).ι) := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    apply (CategoryTheory.mono_iff_injective _).mpr
    rintro ⟨x, a⟩ ⟨y, b⟩ h
    change (x, a.val) = (y, b.val) at h
    have hx : x = y := congrArg (fun q : C.obj d × (Δ[1] : SSet.{u}).obj d => q.1) h
    have ha : a.val = b.val := congrArg (fun q : C.obj d × (Δ[1] : SSet.{u}).obj d => q.2) h
    exact Prod.ext hx (Subtype.ext ha)
  rw [cylinderEndpoints_factor]
  infer_instance

end SerrePositivity.KST.Comparison
