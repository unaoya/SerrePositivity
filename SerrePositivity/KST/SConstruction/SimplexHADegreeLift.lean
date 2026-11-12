module
public import SerrePositivity.KST.SConstruction.SimplexHAGeneratorValues
public import SerrePositivity.KST.SConstruction.SerreCubeDegreeValuesEquiv

/-! # 元の HA 全生成元値からの次数線形射
概要：native HA 成分から、元の全 Serre cube の各次数から実 dg Hom 加群へ線形射を作る。
方針：同じ元の生成元値を既存の全次数復元へ入力し、全生成元上で指定値を回収する。
規約：鎖射の微分可換性は後続で証明する。使われ方：逆 dg Hom 射の実線形成分。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の native HA 成分の全生成元値を持つ、元の Serre cube からの次数線形射。 -/
def simplexHADegreeLift {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b)
    (k : ℤ) : (serreCubeComplex A m).X k ⟶ (homObject A D (s.obj (v 0)) (s.obj b)).X k :=
  serreCubeDegreeLift A m k _ (fun i hi =>
    eqToHom (congrArg (fun d => (homObject A D (s.obj (v 0)) (s.obj b)).X d) hi)
      (simplexHAGeneratorValue A s m i v b hb))

/-- 元の次数線形復元は、元の全 tensor 生成元に指定した同じ native HA 値を回収する。 -/
lemma simplexHADegreeLift_generator {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1)) (hb : v (Fin.last m) < b)
    (k : ℤ) (i : SerreCubeGeneratorIndex m) (hi : serreCubeGeneratorDegree m i = k) :
    simplexHADegreeLift A s m v b hb k
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hi)
          (serreCubeGenerator A m i)) =
      eqToHom (congrArg (fun d => (homObject A D (s.obj (v 0)) (s.obj b)).X d) hi)
        (simplexHAGeneratorValue A s m i v b hb) :=
  serreCubeDegreeLift_generator A m k _ _ i hi

end SerrePositivity.KST.SConstruction
