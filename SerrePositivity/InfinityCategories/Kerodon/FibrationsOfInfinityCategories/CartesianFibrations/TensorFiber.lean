module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SquareTensorProjections

/-!
概要：left fibration と固定パラメーターの積の fiber を元の fiber と同定する。
方針：積の第二成分を固定頂点の定値単体として回収する。
規約：パラメーターの Kan 性は要求しない。
使われ方：積上の四角形の表現条件を各パラメーターで判定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：left fibration と任意のパラメーターの恒等射との積は left fibration。
方針：第一成分を元の射で持ち上げ第二成分は指定された底の単体から取る。
規約：パラメーターの充填性は不要。
使われ方：積上の実際の表現空間の定義。 -/
instance transportTensor_leftFibration {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (p ▷ K) where
  mem := by
    intro A D i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) i hi
    constructor
    intro a b sq
    have hs : CommSq (a ≫ fst E K) i p (b ≫ fst B K) := ⟨by
      have h := congrArg (fun f ↦ f ≫ fst B K) sq.w
      simpa only [Category.assoc, whiskerRight_fst] using h⟩
    refine CommSq.HasLift.mk' { l := lift hs.lift (b ≫ snd B K), fac_left := ?_, fac_right := ?_ }
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst]
        exact hs.fac_left
      · rw [Category.assoc, lift_snd, ← Category.assoc, ← sq.w]
        simp only [Category.assoc, whiskerRight_snd]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst]
        exact hs.fac_right
      · rw [Category.assoc, whiskerRight_snd, lift_snd]

/-- 概要：積射影の指定した対の頂点上の fiber は元の fiber と同型。
方針：第一成分を取り、逆では第二成分に固定頂点の定値単体を入れる。
規約：同型に充填性は不要。
使われ方：表現の fiber 比較をパラメーターごとの比較へ移す。 -/
def transportTensorFiberIso {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (b : B _⦋0⦌) (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ▷ K) (b, k) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b := by
  let F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ▷ K) (b, k) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
    { app d := ↾fun x ↦ ⟨x.val.1, congrArg Prod.fst x.property⟩
      naturality d e α := by
        ext x
        apply Subtype.ext
        rfl }
  let G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ▷ K) (b, k) :=
    { app d := ↾fun x ↦ ⟨(x.val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k d.unop.len), Prod.ext x.property rfl⟩
      naturality d e α := by
        ext x
        apply Subtype.ext
        exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback k α.unop).symm }
  refine { hom := F, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply SSet.hom_ext
    intro d
    ext x
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Prod.snd x.property).symm
  · apply SSet.hom_ext
    intro d
    ext x
    apply Subtype.ext
    rfl

/-- 概要：積の fiber 同型の逆を全空間へ含めると固定パラメーターを挿入する。
方針：各次数の第一成分と定値の第二成分を計算する。
規約：元の fiber の包含も厳密に保つ。
使われ方：pointed space への fiber 比較の可換性。 -/
lemma transportTensorFiberIso_inv_ι {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (b : B _⦋0⦌) (k : K _⦋0⦌) :
    (transportTensorFiberIso p K b k).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ▷ K) (b, k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ lift (𝟙 E) (SSet.const k) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
