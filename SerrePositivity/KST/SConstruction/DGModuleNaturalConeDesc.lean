module
public import SerrePositivity.KST.SConstruction.DGConeDescModuleNaturality
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：同じ全自然な指定零化から実 cone の全厳密比較を構成する。
方針：元二成分の比較を全 Hom end で照合し、指定境界の cone 射へ束ねる。
規約：点ごとの境界証拠に加え、次数 −1 の符号付き全自然性を用いる。
使われ方：指定回転ホモトピーを実 cone 比較の全自然性へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (ξ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "b" => dgModuleNaturalConeArrow R D G H ξ
local notation "T" => dgModuleNaturalConeFunctor R D F G η
variable (s : ∀ x, (moduleHom R D (F.obj x) (H.obj x)).X (-1))
variable (ds : ∀ x, (moduleHom R D (F.obj x) (H.obj x)).d (-1) 0 (s x) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) ((dgModuleNaturalConeArrow R D F G η x) ≫
      (dgModuleNaturalConeArrow R D G H ξ x)))).val)

/-- 概要：同じ指定零化から作る元実 cone 比較の閉零射。
方針：元の実 cone descent を使用する。
規約：指定元・指定終辺を保持。使われ方：全比較の実成分。 -/
def dgModuleNaturalConeDescMap (x : P) :
    ForgetEnrichment.of (Complex R) ((T).obj x) ⟶
      ForgetEnrichment.of (Complex R) (H.obj x) :=
  moduleConeDescOfBoundary R D (a x) (s x) (b x) (ds x)

/-- 概要：元実比較の閉元は同じ二成分の元 descent 元。
方針：閉元からの加群射の逆律を適用する。
規約：元の射を保持。使われ方：全 Hom 上の計算。 -/
lemma dgModuleNaturalConeDescMap_cycle (x : P) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeDescMap R D F G H η ξ s ds x))).val =
      moduleConeDescElement R D (a x) (s x) (b x) :=
  moduleMorphismOfCycle_cycle R D _ _

variable (hs : ∀ x y (n : ℤ) (z : GradedHom R x y n),
    compose R (x := F.obj x) (y := H.obj x) (z := H.obj y)
      ((H.map x y).f n z) (s x) (neg_add_eq_sub 1 n) =
    n.negOnePow • compose R (x := F.obj x) (y := F.obj y) (z := H.obj y)
      (s y) ((F.map x y).f n z) (sub_eq_add_neg n 1).symm)

include hs

/-- 概要：元指定ホモトピーと終辺からの実 cone 比較は全整数次数で自然。
方針：実 Hom end の各評価で元二成分の全自然性を使用する。
規約：元の指定零化と元の実 cone を保持。使われ方：実厳密比較への束ね。 -/
lemma dgModuleNaturalConeDescMap_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (T).obj x) (y := (T).obj y) (z := H.obj y)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeDescMap R D F G H η ξ s ds y))).val (((T).map x y).f n z)
      (add_zero n) =
    compose R (x := (T).obj x) (y := H.obj x) (z := H.obj y)
      ((H.map x y).f n z)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeDescMap R D F G H η ξ s ds x))).val (zero_add n) := by
  rw [dgModuleNaturalConeDescMap_cycle, dgModuleNaturalConeDescMap_cycle]
  exact dgConeDescModule_naturality R D (a x) (a y)
    ((F.map x y).f n z) ((G.map x y).f n z) ((H.map x y).f n z)
    (s x) (s y) (b x) (b y) (hs x y n z)
    (by
      exact (congrArg (fun t => compose R (x := G.obj x) (y := G.obj y) (z := H.obj y)
          t ((G.map x y).f n z) (add_zero n))
        (dgModuleNaturalConeArrow_cycle R D G H ξ y)).trans
        ((ξ.naturality z).trans
          (congrArg (fun t => compose R (x := G.obj x) (y := H.obj x) (z := H.obj y)
            ((H.map x y).f n z) t (zero_add n))
            (dgModuleNaturalConeArrow_cycle R D G H ξ x)).symm))

/-- 概要：同じ指定零化から作る元実 cone の全厳密 dg 比較。
方針：元閉射と証明済み全次数自然性を束ねる。
規約：点ごとの同値選択を使用しない。
使われ方：回転 cone 比較の全関手族化。 -/
def dgModuleNaturalConeDesc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (T) H where
  app x := cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
    (dgModuleNaturalConeDescMap R D F G H η ξ s ds x))
  naturality z := dgModuleNaturalConeDescMap_naturality R D F G H η ξ s ds hs _ _ _ z
/-- 概要：全厳密比較の同じ閉射は元の指定 descent 射。
方針：閉射・閉元対応の逆律を用いる。
規約：比較成分を保持。使われ方：指定包含境界の回収。 -/
lemma dgModuleNaturalConeDesc_arrow (x : P) :
    dgModuleNaturalConeArrow R D (T) H
      (dgModuleNaturalConeDesc R D F G H η ξ s ds hs) x =
      dgModuleNaturalConeDescMap R D F G H η ξ s ds x := by
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _)
      (dgModuleNaturalConeDescMap R D F G H η ξ s ds x)) = _
  exact (closedHomEquiv R (RightModule R D) _ _).symm_apply_apply _

/-- 概要：元全比較は同じ元標準包含の後で指定終辺を厳密回収する。
方針：元閉射の回収と実 cone descent の包含式を合成する。
規約：元終辺と指定零化を保持。使われ方：上二単体の指定包含境界。 -/
lemma dgModuleNaturalConeDesc_inr (x : P) :
    moduleConeInr R D (a x) ≫
      dgModuleNaturalConeArrow R D (T) H
        (dgModuleNaturalConeDesc R D F G H η ξ s ds hs) x = b x :=
  (congrArg (fun t => moduleConeInr R D (a x) ≫ t)
    (dgModuleNaturalConeDesc_arrow R D F G H η ξ s ds hs x)).trans
      (moduleConeDescOfBoundary_inr R D (a x) (s x) (b x) (ds x))
end SerrePositivity.KST.SConstruction
