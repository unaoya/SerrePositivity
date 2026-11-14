module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRetractTransfer
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.ParameterCube

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChainFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All finite ambient chains transferred to the original small value universe。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0137][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0137
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All finite ambient chains transferred to the original small value universe

The actual cube families and their zero/one junction laws use only the
original small SSet model. A chain consists of actual ambient arrows;
it is not a strictly functorial lift of the original base action.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChainFamily
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev chain (T : SSet.{max u v}) (b c : Cᵒᵖ × C) :=
  RetractChainFamily.Chain (ambient hcof hfib) T b c

abbrev family {T : SSet.{max u v}} {b c : Cᵒᵖ × C} (q : chain hcof hfib T b c) :=
  RetractChainFamily.transfer (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib) q

lemma family_substitute {T U : SSet.{max u v}} {b c : Cᵒᵖ × C}
    (j : U ⟶ T) (q : chain hcof hfib T b c) :
    family hcof hfib (q.substitute j) =
      ParameterComposition.substitute j (family hcof hfib q) :=
  RetractChainFamily.transfer_substitute _ _ _ _ _ j q

lemma family_zero_face {T : SSet.{max u v}} {a b c d e : Cᵒᵖ × C}
    (q : chain hcof hfib T a b) (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (g : ambient hcof hfib c ⟶ ambient hcof hfib d) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : chain hcof hfib T d e) :
    family hcof hfib (((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).snoc g t).append r) =
      family hcof hfib ((q.snoc (f ≫ g) t).append r) :=
  RetractChainFamily.zero_face _ _ _ _ _ q f g t r

lemma family_one_face {T : SSet.{max u v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib T a b) (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (r : chain hcof hfib T c d) :
    family hcof hfib ((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)).append r) =
      ParameterComposition.comp
        (family hcof hfib (q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T))) (family hcof hfib r) :=
  RetractChainFamily.one_face _ _ _ _ _ (contraction_over hcof hfib) q f r

def smallFamily {T : SSet.{v}} {b c : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) b c) :
    small hcof hfib b ⊗ T ⟶ small hcof hfib c :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (family hcof hfib q)

lemma smallFamily_substitute {T U : SSet.{v}} {b c : Cᵒᵖ × C}
    (j : U ⟶ T) (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) b c) :
    smallFamily hcof hfib (q.substitute (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map j)) =
      ParameterComposition.substitute j (smallFamily hcof hfib q) := by
  rw [smallFamily, family_substitute]
  ext n x
  rfl

lemma smallFamily_zero_face {T : SSet.{v}} {a b c d e : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b)
    (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (g : ambient hcof hfib c ⟶ ambient hcof hfib d)
    (t : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) d e) :
    smallFamily hcof hfib (((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero _)).snoc g t).append r) =
      smallFamily hcof hfib ((q.snoc (f ≫ g) t).append r) :=
  congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.lowerTensor (family_zero_face hcof hfib q f g t r)

lemma smallFamily_one_face {T : SSet.{v}} {a b c d : Cᵒᵖ × C}
    (q : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) a b)
    (f : ambient hcof hfib b ⟶ ambient hcof hfib c)
    (r : chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) c d) :
    smallFamily hcof hfib ((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one _)).append r) =
      ParameterComposition.comp
        (smallFamily hcof hfib (q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero _)))
        (smallFamily hcof hfib r) := by
  rw [smallFamily, family_one_face]
  ext n x
  rfl

section Parameters
omit [HomotopicalAlgebra.ModelCategory SSet.{v}]

def liftParameter {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map t ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.stdIso 1).hom

lemma liftParameter_zero (T : SSet.{v}) :
    liftParameter.{v, u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) := by
  ext n x
  rfl

lemma liftParameter_one (T : SSet.{v}) :
    liftParameter.{v, u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T) := by
  ext n x
  rfl

lemma liftParameter_comp {T U : SSet.{v}} (j : U ⟶ T)
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} j ≫ liftParameter.{v, u} t = liftParameter.{v, u} (j ≫ t) := by
  ext n x
  rfl

def cubeParameter (n k : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj.{v} n) ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval :=
  liftParameter (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.coordinateOrZero n k)

lemma lifted_face_coordinate_same {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face j ε) ≫
        liftParameter.{v, u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.coordinate j) =
      if ε then _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj n))
        else _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj n)) := by
  rw [liftParameter_comp, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face_coordinate_same]
  cases ε <;> simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.endpoint, Bool.false_eq_true, ↓reduceIte,
    liftParameter_zero, liftParameter_one]

lemma lifted_face_coordinate_other {n : ℕ} (j : Fin (n + 1)) (ε : Bool) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face j ε) ≫
        liftParameter.{v, u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.coordinate (j.succAbove i)) =
      liftParameter.{v, u} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.coordinate i) := by
  rw [liftParameter_comp, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face_coordinate_other]

end Parameters

def cubeChain (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1))) (n : ℕ) :
    chain hcof hfib (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj.{v} n)) (b 0) (b (n + 1)) :=
  RetractChainFamily.Chain.sequence b f (cubeParameter n) (n + 1)

lemma cubeChain_length (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1))) (n : ℕ) :
    (cubeChain hcof hfib b f n).length = n + 1 :=
  RetractChainFamily.Chain.sequence_length _ _ _ _

def cubeFamily (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1))) (n : ℕ) :
    small hcof hfib (b 0) ⊗ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj.{v} n ⟶ small hcof hfib (b (n + 1)) :=
  smallFamily hcof hfib (cubeChain hcof hfib b f n)

lemma cubeFamily_zero (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1))) :
    cubeFamily hcof hfib b f 0 =
      fst (small hcof hfib (b 0)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.obj 0) ≫
        smallTransferArrow hcof hfib (f 0) := by
  unfold cubeFamily smallFamily family cubeChain
  simp only [RetractChainFamily.Chain.sequence]
  rw [RetractChainFamily.transfer_last_parameter (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib)]
  ext n x
  rfl

lemma cubeFamily_one (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1))) :
    cubeFamily hcof hfib b f 1 =
      small hcof hfib (b 0) ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.coordinate (0 : Fin 1) ≫
        (smallTransferCompositionHomotopy hcof hfib (f 0) (f 1)).h := by
  unfold cubeFamily smallFamily family cubeChain
  simp only [RetractChainFamily.Chain.sequence]
  rw [RetractChainFamily.transfer_last_parameter (ambient hcof hfib) (lifted hcof hfib)
    (section_ hcof hfib) (projection hcof hfib) (contraction hcof hfib)
    (contraction_over hcof hfib)]
  ext n x
  rfl

lemma cubeFamily_face (b : ℕ → Cᵒᵖ × C)
    (f : ∀ k, ambient hcof hfib (b k) ⟶ ambient hcof hfib (b (k + 1)))
    {n : ℕ} (j : Fin (n + 1)) (ε : Bool) :
    small hcof hfib (b 0) ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face j ε ≫ cubeFamily hcof hfib b f (n + 1) =
      smallFamily hcof hfib (RetractChainFamily.Chain.sequence b f
        (fun k => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ParameterCube.face j ε) ≫ cubeParameter (n + 1) k)
        (n + 2)) := by
  change ParameterComposition.substitute _ (smallFamily hcof hfib _) = _
  rw [← smallFamily_substitute]
  unfold cubeChain
  rw [RetractChainFamily.Chain.substitute_sequence]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChainFamily
