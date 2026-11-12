module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorSplitOne
public import SerrePositivity.KST.SConstruction.SerreCubeRightFaceGeneratorImage
public import SerrePositivity.KST.SConstruction.SimplexHADegreeLift

/-! # 元の内部一面の全左右生成元対上の HA 復元値
概要：内部一面の実像の HA 線形復元値を、同じ左右生成元の HA 値の実合成で回収。
方針：元の実面像と内部一端点生成元値を、元の同じ指定出力次数へ移す。
規約：元の全生成元と切断頂点を保持。使われ方：全次数の実一面の tensor 制限。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の内部一面の全生成元対の復元値は、同じ左右生成元の HA 値の豊穣順合成。 -/
lemma simplexHADegreeLift_one_tensor_generator {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n : ℕ) (i : SerreCubeGeneratorIndex n) (m : ℕ) (j : SerreCubeGeneratorIndex m)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b) (k : ℤ)
    (hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k) :
    simplexHADegreeLift A s (n + 1 + m) v b hb k
      ((serreCubeRightFace A true n m).hom.f k
        (serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
          k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j))) =
      forward A
        (simplexHAGeneratorValue A s n i (simplexHASplitLeft n m v)
          (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v))
        (simplexHAGeneratorValue A s m j (simplexHASplitRight n m v) b
          (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)) hk := by
  let a := serreCubeGeneratorConcat (n + 1) (i, 1) m j
  have ha : serreCubeGeneratorDegree (n + 1 + m) a = k :=
    (serreCubeGeneratorConcat_degree (n + 1) (i, 1) m j).trans
      ((congrArg (· + serreCubeGeneratorDegree m j)
        (add_zero (serreCubeGeneratorDegree n i))).trans hk)
  let L := simplexHAGeneratorValue A s n i (simplexHASplitLeft n m v)
    (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v)
  let R := simplexHAGeneratorValue A s m j (simplexHASplitRight n m v) b
    (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)
  have h₀ := congrArg (fun x => simplexHADegreeLift A s (n + 1 + m) v b hb k x)
    (serreCubeRightFace_tensor_generator A true n i m j k hk)
  have hv : eqToHom (congrArg (homObject A D (s.obj (v 0)) (s.obj b)).X ha)
      (simplexHAGeneratorValue A s (n + 1 + m) a v b hb) = forward A L R hk := by
    exact eq_of_heq ((complexElement_degree_cast_heq A _ ha _).trans
      ((simplexHAGeneratorValue_split_one_heq A s n i m j v b hb).trans
        (dgForward_heq A rfl rfl rfl rfl rfl hk L L R R rfl hk HEq.rfl HEq.rfl)))
  exact h₀.trans ((simplexHADegreeLift_generator A s (n + 1 + m) v b hb k a ha).trans hv)

end SerrePositivity.KST.SConstruction
