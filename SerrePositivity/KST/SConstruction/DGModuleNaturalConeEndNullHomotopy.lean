module
public import SerrePositivity.KST.SConstruction.DGFunctorHomElementFamily
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeNullHomotopy

/-!
概要：元 cone の指定零化族を、全 dg 関手 Hom end の一つの次数 −1 元として保持する。
方針：既存の全次数符号付き自然性を end への持ち上げに渡す。
規約：対象ごとの零化の任意選択ではなく、元左包含の同じ全族を用いる。
使われ方：元 cone の全関手二単体と実逆回転の全矢印比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "h" => dgModuleNaturalConeNullHomotopyElement R D F G η

/-- 概要：元左包含族は end に必要な豊穣順の符号付き自然性を持つ。
方針：元通常順の全自然性を Koszul 比較で戻す。
規約：全 Hom 次数を保持。使われ方：指定 end 零化元。 -/
lemma dgModuleNaturalConeEndNull_naturality (x y : P) (p n : ℤ) (f : GradedHom R x y p)
    (hn : -1 + p = n) (hn' : p + -1 = n) :
    (-1 * p).negOnePow • forward R ((F.map x y).f p f) ((h) y) hn' =
      forward R ((h) x) (((T).map x y).f p f) hn := by
  obtain rfl : n = p - 1 := by omega
  have he := dgModuleNaturalConeNullHomotopyElement_naturality R D F G η x y p f
  have hs : (-1 * p).negOnePow = p.negOnePow := by simp
  have ht : (p * -1).negOnePow = p.negOnePow := by simp
  rw [forward_eq_signed_compose, forward_eq_signed_compose, he, hs, ht]

/-- 概要：元左包含の同じ全族は元 dg 関手 Hom end の実次数 −1 元。
方針：全 Hom の符号付き自然性から同じ end 元を構成する。
規約：全自然性を実証する。使われ方：全関手二単体の指定零化成分。 -/
def dgModuleNaturalConeEndNullHomotopy :
    (dgFunctorHom R P (RightModule R D) F (T)).X (-1) :=
  dgFunctorHomElementFromFamily R P (RightModule R D) F (T) (-1) (h)
    (dgModuleNaturalConeEndNull_naturality R D F G η)

/-- 概要：同じ全関手零化元の評価は元 cone の指定左包含。
方針：同じ end 元の厳密成分回収を使用。
規約：元成分を保持。使われ方：元三辺と零化二単体の照合。 -/
lemma dgModuleNaturalConeEndNullHomotopy_π (x : P) :
    (dgFunctorHomπ R P (RightModule R D) F (T) x).f (-1)
      (dgModuleNaturalConeEndNullHomotopy R D F G η) = (h) x :=
  dgFunctorHomElementFromFamily_π R P (RightModule R D) F (T) (-1) (h)
    (dgModuleNaturalConeEndNull_naturality R D F G η) x

/-- 概要：元 end 零化の微分は全対象で元比較と元 cone 包含の合成を回収する。
方針：end 評価の chain 性と元左包含の指定微分を合成する。
規約：元比較と元包含を変更しない。使われ方：指定全関手二単体の境界認証。 -/
lemma dgModuleNaturalConeEndNullHomotopy_d_π (x : P) :
    (dgFunctorHomπ R P (RightModule R D) F (T) x).f 0
      ((dgFunctorHom R P (RightModule R D) F (T)).d (-1) 0
        (dgModuleNaturalConeEndNullHomotopy R D F G η)) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D F G η x ≫
          moduleConeInr R D (dgModuleNaturalConeArrow R D F G η x)))).val := by
  have hc := congrArg (fun fm => fm (dgModuleNaturalConeEndNullHomotopy R D F G η))
    ((dgFunctorHomπ R P (RightModule R D) F (T) x).comm (-1) 0).symm
  change (dgFunctorHomπ R P (RightModule R D) F (T) x).f 0
      ((dgFunctorHom R P (RightModule R D) F (T)).d (-1) 0
        (dgModuleNaturalConeEndNullHomotopy R D F G η)) =
    (homObject R (RightModule R D) (F.obj x) ((T).obj x)).d (-1) 0
      ((dgFunctorHomπ R P (RightModule R D) F (T) x).f (-1)
        (dgModuleNaturalConeEndNullHomotopy R D F G η)) at hc
  exact hc.trans ((congrArg
    ((homObject R (RightModule R D) (F.obj x) ((T).obj x)).d (-1) 0)
    (dgModuleNaturalConeEndNullHomotopy_π R D F G η x)).trans
      (dgModuleNaturalConeNullHomotopyElement_d R D F G η x))

end SerrePositivity.KST.SConstruction
