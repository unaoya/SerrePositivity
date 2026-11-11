module
public import SerrePositivity.KST.SConstruction.SimplexHAOneTensorGenerator
public import SerrePositivity.KST.SConstruction.SerreCubeTensorComposition

/-! # 元の内部一面への左右 Hom 鎖射による制限
概要：左右の実 Hom 鎖射が元の線形復元を回収すれば、一面制限はその実 tensor 合成。
方針：元の全左右生成元対と HA 値の内部切断式で同じ全次数の線形射を判定する。
規約：左右の実鎖射とその次数成分の回収を明記。使われ方：全次元の復元鎖射の帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 左右の実鎖射が元の復元を回収すれば、内部一面への制限は同じ実 tensor 合成。 -/
lemma simplexHADegreeLift_one_tensor_restriction {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n m : ℕ) (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b)
    (F : serreCubeComplex A n ⟶ homObject A D (s.obj (v 0)) (s.obj (simplexHASplitCut n m v)))
    (G : serreCubeComplex A m ⟶ homObject A D (s.obj (simplexHASplitCut n m v)) (s.obj b))
    (hF : ∀ k, F.f k = simplexHADegreeLift A s n (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v) k)
    (hG : ∀ k, G.f k = simplexHADegreeLift A s m (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb) k) (k : ℤ) :
    (serreCubeRightFace A true n m).hom.f k ≫ simplexHADegreeLift A s (n + 1 + m) v b hb k =
      (serreCubeTensorComposition A n m F G).f k := by
  apply serreCube_tensor_generator_hom_ext A n m k
  intro i j hk
  have hf := (congrArg (fun f => f (serreCubeGenerator A n i))
    (hF (serreCubeGeneratorDegree n i))).trans
    (simplexHADegreeLift_generator A s n (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v) _ i rfl)
  have hg := (congrArg (fun f => f (serreCubeGenerator A m j))
    (hG (serreCubeGeneratorDegree m j))).trans
    (simplexHADegreeLift_generator A s m (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb) _ j rfl)
  have hcomp := congrArg₂ (fun f g => forward A f g hk) hf hg
  have hright := (serreCubeTensorComposition_apply A n m F G _ _ k hk
    (serreCubeGenerator A n i) (serreCubeGenerator A m j)).trans hcomp
  exact (simplexHADegreeLift_one_tensor_generator A s n i m j v b hb k hk).trans hright.symm

end SerrePositivity.KST.SConstruction
