module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialFiberMapTransport
public import SerrePositivity.InfinityCategories.Stable.CoconeMappingPiZero
public import SerrePositivity.InfinityCategories.F1.CosliceTriangleFiber

/-!
概要：部分図式への余錐の制限を正規化し、頂点に沿う輸送後の制限の Hom を計算する。
方針：図式の等式による移送を含む底上の制限へ、left fibration の transport の自然性を適用する。
規約：余極限性は共通部分の図式にだけ要求し、元の部分余錐の輸送を保つ。
使われ方：span の余錐の二枝から、共通部分の境界の連結成分の一致を導く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A C X : SSet.{u}} {p : A ⟶ X} (F : C ⟶ X) (i : A ⟶ C) (hi : i ≫ F = p)

/-- 部分図式の表示を正規化した、元の余錐から共通部分の余錐への制限。 -/
def normalizedCoconeRestriction : sliceUnder F ⟶ sliceUnder p :=
  sliceUnderRestrict F i ≫ eqToHom (congrArg sliceUnder hi)

/-- 正規化した制限は余錐の頂点への射影を厳密に保つ。 -/
lemma normalizedCoconeRestriction_projection :
    normalizedCoconeRestriction F i hi ≫ sliceUnderProjection p = sliceUnderProjection F := by
  have ht {a b : A ⟶ X} (h : a = b) :
      eqToHom (congrArg sliceUnder h) ≫ sliceUnderProjection b = sliceUnderProjection a := by
    cases h
    exact Category.id_comp _
  rw [normalizedCoconeRestriction, Category.assoc, ht hi, sliceUnderRestrict_projection]

/-- 指定した頂点上の余錐空間への、正規化した制限。 -/
def normalizedCoconeRestrictionFiber (y : X _⦋0⦌) :
    coconeMappingSpace F y ⟶ coconeMappingSpace p y :=
  vertexFiberMap (sliceUnderProjection F) (sliceUnderProjection p)
    (normalizedCoconeRestriction F i hi) (normalizedCoconeRestriction_projection F i hi) y

/-- 固定頂点の正規化した制限は、通常の fiber の制限と図式の等式による移送の合成。 -/
lemma normalizedCoconeRestrictionFiber_eq (y : X _⦋0⦌) :
    normalizedCoconeRestrictionFiber F i hi y = cosliceRestrictionFiberMap F i y ≫
      eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) hi) := by
  cases hi
  simp only [normalizedCoconeRestrictionFiber, normalizedCoconeRestriction,
    eqToHom_refl, Category.comp_id]
  rfl

/-- 部分余錐を輸送してから共通部分で Hom を読むと、元の制限の Hom と底の辺の合成になる。 -/
lemma coconeMappingSpacePiZeroEquiv_restrict_transport [Quasicategory X]
    (c : JoinCocone p) (hc : IsColimitCone c) {a b : X _⦋0⦌} (e : X.Edge a b)
    (v : SSet.π₀ (coconeMappingSpace F a)) :
    coconeMappingSpacePiZeroEquiv c hc b
        (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi b)
          (SSet.mapπ₀ (edgeTransport (sliceUnderProjection F) e) v)) =
      coconeMappingSpacePiZeroEquiv c hc a
          (SSet.mapπ₀ (normalizedCoconeRestrictionFiber F i hi a) v) ≫
        SSet.Truncated.HomotopyCategory.homMk e.toTruncated :=
  leftFibrationInitialFiberPiZeroEquiv_map_transport (sliceUnderProjection F)
    (sliceUnderProjection p) (normalizedCoconeRestriction F i hi)
      (normalizedCoconeRestriction_projection F i hi) c hc e v

end
end SerrePositivity.InfinityCategories.HomotopyLimits
