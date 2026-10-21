module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorPairFaces
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorSpan

/-! # 元の左右 tensor 生成元による全次数の線形射の判定
概要：元の左右ブロックの全生成元対で、元の連結 cube 上の線形射を判定する。
方針：添字の分解・連結の逆律と、実 tensor 合成元の生成元表示を使う。
規約：元の指定次数と全生成元を保持。使われ方：実一面の左右 tensor 制限の判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の左右の全生成元対への作用は、元の連結 cube の同じ次数線形射を判定する。 -/
lemma serreCube_tensor_generator_hom_ext (n m : ℕ) (k : ℤ) {M : ModuleCat.{u} A}
    {f g : (serreCubeComplex A (n + m)).X k ⟶ M}
    (h : ∀ (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex m)
      (hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k),
      f (serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
        k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j)) =
      g (serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
        k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j))) : f = g := by
  apply serreCube_degree_hom_ext A (n + m) k
  intro a ha
  obtain ⟨⟨i, j⟩, rfl⟩ := serreCubeGeneratorConcat_surjective n m a
  have hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k :=
    (serreCubeGeneratorConcat_degree n i m j).symm.trans ha
  have he := serreCubeTensorPair_generator A n i m j k hk
  exact (congrArg (fun x => f x) he).symm.trans ((h i j hk).trans (congrArg (fun x => g x) he))

/-- 元の左斉次次数の移送は、同じ出力次数の実 tensor 合成元を変えない。 -/
lemma serreCubeTensorPair_cast_left (n m : ℕ) {p p' q k : ℤ} (hp : p = p')
    (hk : p + q = k) (hk' : p' + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreCubeComplex A m).X q) :
    serreCubeTensorPair A n m p' q k hk'
      (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hp) x) y =
      serreCubeTensorPair A n m p q k hk x y := by
  cases hp
  rfl

end SerrePositivity.KST.SConstruction
