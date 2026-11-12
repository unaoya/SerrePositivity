module
public import SerrePositivity.KST.ProExcision.LinearizedBarCylinder
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints
public import SerrePositivity.KST.ProExcision.ActionBarFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MHomotopyHomology

/-!
# m 次同変ホモトピーの作用 bar への移送

概要：係数の m 次同変ホモトピーは作用 bar の自由整数加群の m 次ホモトピーを与える。
方針：全次数の線形区間写像を持ち上げ、語を固定した係数包含で両端を同定する。
規約：KST Definition A.3、Lemma A.4。零次を含み、両端の幾何的射は同じ G 上の同変射。
使われ方：A.1 と組み合わせる前の係数作用 bar のホモロジー比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G : SimplicialObject MonCat.{u}} {X Y : SSet.{u}}
variable {A : SimplicialSetAction G X} {B : SimplicialSetAction G Y}

/-- 概要：係数の区間の指定端点が幾何的射なら、bar の同じ端点もその誘導射。
方針：基底上で区間写像を評価し、係数包含の同変射についての自然性で復元する。
規約：KST Lemma A.4、G の基底射は恒等。
使われ方：持ち上げた m 次ホモトピーの両端条件。 -/
lemma linearizedActionBarCylinder_endpoint_generator
    (H : EquivariantLinearizedCylinderMap A B) (f : SimplicialSetActionHom A B)
    (hf : f.base = 𝟙 G) (n : SimplexCategoryᵒᵖ) (ε : Fin 2)
    (hε : ∀ x : X.obj n, H.h.app n
      (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 ε n))) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (f.hom.app n x))
    (p : (setActionBar A).obj n) :
    linearizedActionBarCylinderApp H n
      (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 ε n))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator ((setActionBarMap f).app n p) := by
  rw [linearizedActionBarCylinderApp_generator, hε]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map
      (↾(setActionBarFiberSection B n ((setActionBarProjection A).app n p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (f.hom.app n (p.obj 0).val)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
  have hs := setActionBarFiberSection_map f n ((setActionBarProjection A).app n p) (p.obj 0).val
  rw [hf, monoidBarMap_id] at hs
  change (setActionBarMap f).app n
      (setActionBarFiberSection A n ((setActionBarProjection A).app n p) (p.obj 0).val) =
    setActionBarFiberSection B n ((setActionBarProjection A).app n p)
      (f.hom.app n (p.obj 0).val) at hs
  rw [setActionBarFiberSection_reconstruct] at hs
  exact hs.symm

/-- 概要：m 次同変ホモトピーを係数作用 bar の m 次ホモトピーへ送る。
方針：同変区間写像の単体的持ち上げと、各次数の端点の基底公式を使う。
規約：KST Lemma A.4。G の射を恒等とする二つの同変射。結論を追加仮定にしない。
使われ方：作用 bar の複体ホモロジー写像を次数 ≤m で比較する。 -/
def linearizedActionBarMHomotopy (f g : SimplicialSetActionHom A B)
    (hf : f.base = 𝟙 G) (hg : g.base = 𝟙 G) {m : ℕ}
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap f.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap g.hom) m)
    (hH : ∀ n (a : G.obj n),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (linearizedSetAction A n a) (𝟙 _) ≫ H.h.app n =
        H.h.app n ≫ linearizedSetAction B n a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (setActionBarMap f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap (setActionBarMap g)) m := by
  let C : EquivariantLinearizedCylinderMap A B := ⟨H.h, hH⟩
  refine { h := linearizedActionBarCylinderMap C, h₀ := ?_, h₁ := ?_ }
  · intro q hq
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext (X := (setActionBar A).obj (op ⦋q⦌))
    intro p
    change linearizedActionBarCylinderApp C (op ⦋q⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ (setActionBar A)).app (op ⦋q⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBarMap f).app (op ⦋q⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)
    rw [linearizedEndpoint₀_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
    refine linearizedActionBarCylinder_endpoint_generator C f hf (op ⦋q⦌) 0 ?_ p
    intro x
    have he := congrArg (fun a ↦ a.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) (H.h₀ q hq)
    change H.h.app (op ⦋q⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X).app (op ⦋q⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (f.hom.app (op ⦋q⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) at he
    rw [linearizedEndpoint₀_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator] at he
    exact he
  · intro q hq
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext (X := (setActionBar A).obj (op ⦋q⦌))
    intro p
    change linearizedActionBarCylinderApp C (op ⦋q⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ (setActionBar A)).app (op ⦋q⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBarMap g).app (op ⦋q⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p)
    rw [linearizedEndpoint₁_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
    refine linearizedActionBarCylinder_endpoint_generator C g hg (op ⦋q⦌) 1 ?_ p
    intro x
    have he := congrArg (fun a ↦ a.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) (H.h₁ q hq)
    change H.h.app (op ⦋q⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X).app (op ⦋q⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (g.hom.app (op ⦋q⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) at he
    rw [linearizedEndpoint₁_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator] at he
    exact he

end SerrePositivity.KST.ProExcision
