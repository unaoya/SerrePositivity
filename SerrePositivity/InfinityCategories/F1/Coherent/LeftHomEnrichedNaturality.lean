module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftFlagComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PinchedLeftCoordinates
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantFiber

/-!
概要：左 pinched 写像空間の関手性と coherent な左 Hom 比較の豊穣関手に関する自然性。
方針：右 Hom の関手性を反転し、coherent nerve の反対の逆射の自然性を適用する。
規約：局所 Kan 性なしで射そのものの全次数の可換性を示す。
使われ方：Kerodon §4.6.7、Corollary 5.6.0.6、評価関手に沿う左 fiber 比較の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の射は左 pinched 写像空間の射を誘導する。
方針：反転した射を右 Hom に作用させて、結果を反転する。
規約：両端点は元の射で写す。
使われ方：Kerodon §4.6.7、左 Hom 比較の自然性の標的の射。 -/
def pinchedHomLeftMap {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌) :
    pinchedHomLeft x y ⟶
      pinchedHomLeft (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  SSet.opFunctor.map (pinchedHomMap (SSet.opFunctor.map f)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))

/-- 概要：左 Hom の端点を等号で移送しても元の左 coherent 単体は変わらない。
方針：二端点の等号を消去する。
規約：全次数で成立し、充填性を要求しない。
使われ方：Kerodon §4.6.7、標準頂点への正規化を含む自然性の計算。 -/
lemma pinchedHomLeft_eqToHom_app_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal n
      ((eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft a b) hx hy)).app (Opposite.op ⦋n⦌) s) =
    pinchedLeftSimplexVal n s := by
  subst x'
  subst y'
  rfl

/-- 概要：左 Hom の射による作用は元の左 coherent 単体への後合成になる。
方針：反転した右 Hom の単体の値を二重反転から取り出す。
規約：単体圏の次数は任意。
使われ方：Kerodon §4.6.7、coherent 比較の射への自然性を単体で確認する。 -/
lemma pinchedHomLeftMap_app_val {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {n : ℕ} (s : (pinchedHomLeft x y) _⦋n⦌) :
    pinchedLeftSimplexVal n ((pinchedHomLeftMap f x y).app (Opposite.op ⦋n⦌) s) =
      f.app (Opposite.op ⦋n + 1⦌) (pinchedLeftSimplexVal n s) := rfl

/-- 概要：豊穣関手が標準二頂点の左 pinched 写像空間に誘導する射。
方針：coherent nerve の射を左 Hom に適用し、二端点を像の標準頂点へ正規化する。
規約：coherent nerve の射による実際の後合成を使う。
使われ方：Kerodon §4.6.7、豊穣評価に沿う左 Hom 比較の可換図式。 -/
noncomputable def coherentLeftPinchedHomMap
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (x y : C) :
    pinchedHomLeft (coherentNerveVertex x) (coherentNerveVertex y) ⟶
      pinchedHomLeft (coherentNerveVertex (F.obj x)) (coherentNerveVertex (F.obj y)) :=
  pinchedHomLeftMap (coherentNerveMap F) (coherentNerveVertex x) (coherentNerveVertex y) ≫
    eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft a b)
      (coherentNerveMap_vertex F x) (coherentNerveMap_vertex F y))

/-- 概要：反対 nerve の逆写像を定める単体の構成は豊穣関手による後合成と可換。
方針：反対 nerve の逆射の自然性を各単体で評価し、反転の同値で値を戻す。
規約：C と D は対象および Hom の宇宙を共有する。
使われ方：Kerodon §4.6.7、左 Hom の標準比較の自然性の単体ごとの計算。 -/
lemma coherentOppositeInverseSimplex_postcomp
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) {n : ℕ}
    (σ : (SimplicialNerve Cᵒᵖ) _⦋n⦌) :
    (HomotopyLimits.coherentOppositeInverseSimplex σ).comp SSet F =
      HomotopyLimits.coherentOppositeInverseSimplex
        (σ.comp SSet (HomotopyLimits.coherentEnrichedFunctorOp F)) := by
  have h := congrArg (fun f : SimplicialNerve Cᵒᵖ ⟶ (SimplicialNerve D).op ↦
    f.app (Opposite.op ⦋n⦌) σ) (HomotopyLimits.coherentNerveOppositeInverse_post F)
  change SSet.opObjEquiv.symm
      (HomotopyLimits.coherentOppositeInverseSimplex
        (σ.comp SSet (HomotopyLimits.coherentEnrichedFunctorOp F))) =
    SSet.opObjEquiv.symm
      ((HomotopyLimits.coherentOppositeInverseSimplex σ).comp SSet F) at h
  exact SSet.opObjEquiv.symm.injective h.symm

/-- 概要：左 Hom の標準比較は豊穣関手の作用と coherent nerve 上の作用を全次数で結ぶ。
方針：端点の移送を外し、反転した右 Hom 比較の後合成と反対 nerve の逆射の自然性を使う。
規約：係数の豊穣 Hom は反転してから宇宙を持ち上げる。
使われ方：Kerodon §4.6.7、Corollary 5.6.0.6、豊穣評価に沿う実際の左 fiber 比較の自然性。 -/
lemma coherentLeftHomComparison_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (x y : C) :
    HomotopyLimits.coherentLeftHomComparison x y ≫ coherentLeftPinchedHomMap F x y =
      (SSet.uliftFunctor.{v, u}).map (SSet.opFunctor.map (F.map x y)) ≫
        HomotopyLimits.coherentLeftHomComparison (F.obj x) (F.obj y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply pinchedLeftSimplexVal_injective n
  change pinchedLeftSimplexVal n
      ((eqToHom (congrArg₂ (fun a b ↦ pinchedHomLeft a b)
        (coherentNerveMap_vertex F x) (coherentNerveMap_vertex F y))).app _
        ((pinchedHomLeftMap (coherentNerveMap F) _ _).app _
          ((HomotopyLimits.coherentLeftHomComparison x y).app _ s))) = _
  rw [pinchedHomLeft_eqToHom_app_val (coherentNerveMap_vertex F x)
    (coherentNerveMap_vertex F y), pinchedHomLeftMap_app_val]
  change (coherentNerveMap F).app _
      (pinchedLeftSimplexVal n ((HomotopyLimits.coherentLeftHomComparison x y).app _
        (ULift.up s.down))) =
    pinchedLeftSimplexVal n
      ((HomotopyLimits.coherentLeftHomComparison (F.obj x) (F.obj y)).app _
        (ULift.up ((SSet.opFunctor.map (F.map x y)).app _ s.down)))
  rw [HomotopyLimits.coherentLeftHomComparison_simplex,
    HomotopyLimits.coherentLeftHomComparison_simplex]
  change (HomotopyLimits.coherentOppositeInverseSimplex
      (coherentHomComparisonSimplex (X := Opposite.op y) (Y := Opposite.op x)
        (SSet.opObjEquiv s.down))).comp SSet F = _
  rw [coherentOppositeInverseSimplex_postcomp,
    coherentHomComparisonSimplex_postcomp]
  rfl

end SerrePositivity.InfinityCategories
