module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingSpan

/-!
概要：頂点 fiber の誘導射の fiber は元の全空間の射の fiber と同型である。
方針：二重の fiber の固定条件を、同じ単体に対する二つの等式として往復する。
規約：quasicategory 性や fibration 性は要求しない厳密な同型。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の比較 span の strict fiber と pinched Hom の同定。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：同じ底上の比較の fiber 内での fiber は、元の比較の対応する頂点での fiber。
方針：二重の部分型から底の固定条件を忘れ、逆には可換性からその条件を回収する。
規約：底の可換条件の証明に依存しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の写像空間の比較 span の strict fiber の計算。 -/
def vertexFiberMapFiberIso {E E' B : SSet.{u}} (p : E ⟶ B) (q : E' ⟶ B)
    (f : E ⟶ E') (hf : f ≫ q = p) (b : B.obj (Opposite.op ⦋0⦌))
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) d ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber f d.val where
  hom :=
    { app := fun _ ↦ ↾fun s ↦ ⟨s.val.val, congrArg Subtype.val s.property⟩
      naturality := by intro k l α; rfl }
  inv :=
    { app := fun k ↦ ↾fun t ↦ ⟨⟨t.val, by
        have h := ConcreteCategory.congr_hom (NatTrans.congr_app hf k) t.val
        change q.app k (f.app k t.val) = p.app k t.val at h
        calc
          _ = q.app k (f.app k t.val) := h.symm
          _ = q.app k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant d.val k.unop.len) := congrArg (q.app k) t.property
          _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (q.app (Opposite.op ⦋0⦌) d.val) k.unop.len :=
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map q d.val k.unop.len
          _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b k.unop.len := congrArg
            (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z k.unop.len)
              (d.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))⟩, by
                apply Subtype.ext
                exact t.property⟩
      naturality := by
        intro k l α
        apply ConcreteCategory.hom_ext
        intro t
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro k
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro k
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    rfl

/-- 概要：right fibration の比較 span の始点評価の strict fiber は元の pinched Hom。
方針：二重 fiber の同型に、点上の slice の fiber と右 pinched Hom の同型を続ける。
規約：同型自体には right fibration 性も quasicategory 性も不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の錐の写像空間を比較の fiber として表す段階。 -/
noncomputable def rightFibrationMappingEvaluationFiberIso {E B : SSet.{u}} (r : E ⟶ B)
    (c : E.obj (Opposite.op ⦋0⦌)) (x : B.obj (Opposite.op ⦋0⦌))
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r x).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) d ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom d.val c :=
  (vertexFiberMapFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c) ≫ r) r
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)) rfl x d).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso d.val c).symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
