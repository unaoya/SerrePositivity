module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCell
public import SerrePositivity.KST.SConstruction.SerreIntervalTensorExt

/-! # 元の全 Serre cube の端点・辺 tensor 生成元
概要：元の各座標で零端点・一端点・辺を選ぶ全ての tensor 生成元と次数を与える。
方針：元の有限 tensor 冪と同じ順に、元の区間生成元を再帰的に tensor する。
規約：元の複体と因子順を保持。使われ方：native HA 成分からの全 Hom 生成元復元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 元の全座標で零端点・一端点・辺を選ぶ、元の tensor の順序付き添字。 -/
def SerreCubeGeneratorIndex : ℕ → Type
  | 0 => PUnit
  | n + 1 => SerreCubeGeneratorIndex n × Fin 3

/-- 元の端点・辺 tensor 生成元の cochain 次数。 -/
def serreCubeGeneratorDegree : (n : ℕ) → SerreCubeGeneratorIndex n → ℤ
  | 0, _ => 0
  | n + 1, i => serreCubeGeneratorDegree n i.1 + serreIntervalGeneratorDegree i.2

variable (A : Type u) [CommRing A]

/-- 元の区間の端点・辺を同じ元の有限 tensor 冪で掛けた、全 Serre cube 生成元。 -/
def serreCubeGenerator : (n : ℕ) → (i : SerreCubeGeneratorIndex n) →
    (serreCubeComplex A n).X (serreCubeGeneratorDegree n i)
  | 0, _ => (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)).val
  | n + 1, i => ιTensorObj (serreCubeComplex A n) (serreInterval A)
      (serreCubeGeneratorDegree n i.1) (serreIntervalGeneratorDegree i.2)
      (serreCubeGeneratorDegree (n + 1) i) rfl
        (serreCubeGenerator n i.1 ⊗ₜ[A] serreIntervalGenerator A i.2)

/-- 元の一段の生成元を指定次数で読むと、同じ双次数包含による元の tensor。 -/
lemma serreCubeGenerator_succ_cast (n : ℕ) (i : SerreCubeGeneratorIndex n) (j : Fin 3)
    (k : ℤ) (hk : serreCubeGeneratorDegree n i + serreIntervalGeneratorDegree j = k) :
    eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1)).X d) hk)
        (serreCubeGenerator A (n + 1) (i, j)) =
      ιTensorObj (serreCubeComplex A n) (serreInterval A)
        (serreCubeGeneratorDegree n i) (serreIntervalGeneratorDegree j) k hk
        (serreCubeGenerator A n i ⊗ₜ[A] serreIntervalGenerator A j) := by
  cases hk
  rfl

end SerrePositivity.KST.SConstruction
