module
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeTransport

/-! # 固定部分を持つ prism の収縮と right anodyne 性

概要：恒等射から部分複体への収縮へ向かい、その部分を固定する prism は right anodyne 性を与える。
方針：終点の持ち上げと固定部分の prism を貼り、終点ホーンとの pushout-product を持ち上げる。
規約：収縮と固定条件は単体集合の射の厳密な等式で指定する。
使われ方：S4 の右 span を含む部分長方形の cofinal な制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：部分複体を固定した終点への prism の収縮があれば、その包含は right anodyne。
方針：right fibration に対する持ち上げを、固定部分と収縮先で指定し、prism の右 anodyne 性で延長する。
規約：H は時刻零で恒等射、時刻一で r の像への包含。
使われ方：貼り合わせの coslice を、終端側の span に制限する。 -/
lemma stable_rightAnodyneExtensions_of_prism_retraction {B : SSet.{u}} (A : B.Subcomplex)
    (r : B ⟶ (A : SSet.{u})) (hr : A.ι ≫ r = 𝟙 (A : SSet.{u}))
    (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ H = 𝟙 B)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ H = r ≫ A.ι)
    (hA : (Δ[1] ◁ A.ι) ≫ H = snd (Δ[1] : SSet.{u}) (A : SSet.{u}) ≫ A.ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A.ι := by
  intro E D p hp
  constructor
  intro a b sq
  let S := horn.{u} 1 1
  let q := Subcomplex.unionProd.isPushout S A
  let G := snd (Δ[1] : SSet.{u}) (A : SSet.{u}) ≫ a
  let T := snd (S : SSet.{u}) B ≫ r ≫ a
  have hw : (S.ι ▷ (A : SSet.{u})) ≫ G = ((S : SSet.{u}) ◁ A.ι) ≫ T := by
    change snd (S : SSet.{u}) (A : SSet.{u}) ≫ a =
      snd (S : SSet.{u}) (A : SSet.{u}) ≫ A.ι ≫ r ≫ a
    rw [← Category.assoc A.ι, hr, Category.id_comp]
  let C := q.desc G T hw
  have hCG : Subcomplex.unionProd.ι₁ S A ≫ C = G := q.inl_desc _ _ _
  have hCT : Subcomplex.unionProd.ι₂ S A ≫ C = T := q.inr_desc _ _ _
  have hbase : C ≫ p = (Subcomplex.unionProd S A).ι ≫ H ≫ b := by
    apply q.hom_ext
    · rw [← Category.assoc, hCG, ← Category.assoc (Subcomplex.unionProd.ι₁ S A),
        Subcomplex.unionProd.ι₁_ι]
      rw [← Category.assoc (Δ[1] ◁ A.ι) H b, hA]
      dsimp only [G]
      simp only [Category.assoc, sq.w]
    · rw [← Category.assoc, hCT, ← Category.assoc (Subcomplex.unionProd.ι₂ S A),
        Subcomplex.unionProd.ι₂_ι, Category.assoc]
      dsimp only [T, S]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_hornOneLast_inclusion]
      simp only [Category.assoc]
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B) H b, h₁]
      simp only [Category.assoc, sq.w]
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (Subcomplex.unionProd S A).ι :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightAnodyneExtensions_pushoutObjObj_point A.ι
      (Subcomplex.unionProd.pushoutObjObj S A)
  have := hl p hp
  let hs : CommSq C (Subcomplex.unionProd S A).ι p (H ≫ b) := ⟨hbase⟩
  let L := hs.lift
  have hL : (Δ[1] ◁ A.ι) ≫ L = G := by
    rw [← Subcomplex.unionProd.ι₁_ι S A, Category.assoc]
    change Subcomplex.unionProd.ι₁ S A ≫ ((Subcomplex.unionProd S A).ι ≫ hs.lift) = G
    rw [hs.fac_left, hCG]
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ L, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc A.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B) L, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
      Category.assoc, hL]
    rfl
  · rw [Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ (hs.lift ≫ p) = b
    rw [hs.fac_right, ← Category.assoc, h₀, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
