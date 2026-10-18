module

public import SerrePositivity.KST.Comparison.Homology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# 退化整数鎖複体の収縮

概要：正規化射影の補射影の像として退化複体を構成し、実際の鎖収縮を与える。
方針：Mathlib の Dold–Kan 射影 Q∞ の零ホモトピーを、その像の分裂に制限する。
規約：Weibel K-book III、Waldhausen LNM 1126 §1.7・§1.8。正規化比較は射影による証明経路を採る。
使われ方：整数ホモロジーで退化単体を取り除けることの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：非正規化整数鎖複体の退化部分への射影。
方針：自由単体的アーベル群の Q∞ を使う。
規約：Q∞ は恒等射から正規化射影 P∞ を引いた鎖写像。
使われ方：退化鎖複体の像による構成。
-/
def integralDegenerateProjection (X : SSet.{u}) :
    unnormalizedIntegralChains.obj X ⟶ unnormalizedIntegralChains.obj X :=
  DoldKan.QInfty (X := freeAbelianSimplicialFunctor.obj X)

/--
概要：整数退化鎖複体。
方針：複体のアーベル圏で退化射影の像を取る。
規約：単なる次数ごとの群でなく微分を備えた複体。
使われ方：退化部分の鎖収縮とホモロジーの消滅。
-/
def degenerateIntegralChains (X : SSet.{u}) : ChainComplex AddCommGrpCat.{u} ℕ :=
  image (integralDegenerateProjection X)

/--
概要：退化鎖複体の包含と像への射は恒等射に合成する。
方針：Q∞ の冪等性から像の全射と単射を消去する。
規約：包含の向きは退化複体から非正規化複体。
使われ方：零ホモトピーを像へ制限する。
-/
theorem degenerateIntegralChains_split (X : SSet.{u}) :
    image.ι (integralDegenerateProjection X) ≫ factorThruImage (integralDegenerateProjection X) =
      𝟙 (degenerateIntegralChains X) := by
  have hq : integralDegenerateProjection X ≫ integralDegenerateProjection X =
      integralDegenerateProjection X :=
    DoldKan.QInfty_idem (X := freeAbelianSimplicialFunctor.obj X)
  apply (cancel_epi (factorThruImage (integralDegenerateProjection X))).mp
  apply (cancel_mono (image.ι (integralDegenerateProjection X))).mp
  simpa only [degenerateIntegralChains, Category.assoc, image.fac, image.fac_assoc,
    Category.id_comp, Category.comp_id] using
    hq

/--
概要：退化射影の実際の零ホモトピー。
方針：正規化射影から恒等射への Mathlib のホモトピーを引き算する。
規約：鎖ホモトピーを存在仮定として置かない。
使われ方：退化複体の収縮。
-/
def integralDegenerateProjectionNullHomotopy (X : SSet.{u}) :
    Homotopy (integralDegenerateProjection X) 0 :=
  Homotopy.equivSubZero.toFun
    (DoldKan.homotopyPInftyToId (freeAbelianSimplicialFunctor.obj X)).symm

/--
概要：退化整数鎖複体の恒等射は零射と鎖ホモトピックである。
方針：Q∞ の零ホモトピーを包含と像への射で挟み、分裂恒等式を使う。
規約：全ての単体集合に対する実際の収縮。
使われ方：退化部分の全次数のホモロジー消滅。
-/
def degenerateIntegralChainsContraction (X : SSet.{u}) :
    Homotopy (𝟙 (degenerateIntegralChains X)) 0 := by
  let q := integralDegenerateProjection X
  let i := image.ι q
  let p := factorThruImage q
  have hi : i ≫ p = 𝟙 (image q) := degenerateIntegralChains_split X
  have hq : q = p ≫ i := (image.fac q).symm
  have h := ((integralDegenerateProjectionNullHomotopy X).compLeft i).compRight p
  have he : (i ≫ q) ≫ p = 𝟙 (image q) := by
    calc
      (i ≫ q) ≫ p = (i ≫ (p ≫ i)) ≫ p :=
        congrArg (fun t => (i ≫ t) ≫ p) hq
      _ = (i ≫ p) ≫ (i ≫ p) := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hi, Category.id_comp]
  exact (Homotopy.ofEq he.symm).trans
    (h.trans (Homotopy.ofEq (by simp)))

/--
概要：退化整数鎖複体のホモロジーは全次数で零である。
方針：構成した鎖収縮をホモロジーへ渡すと恒等射が零射になる。
規約：収縮からの帰結であり、消滅を仮定しない。
使われ方：正規化によるホモロジー計算。
-/
theorem degenerateIntegralChains_homology_isZero (X : SSet.{u}) (n : ℕ) :
    IsZero ((degenerateIntegralChains X).homology n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using
    (degenerateIntegralChainsContraction X).homologyMap_eq n

/--
概要：退化射影を零に送ることと、全ての退化を零に送ることは同値である。
方針：Mathlib の Q∞ の退化像による分解と、退化の正規化射影による消滅を使う。
規約：各次数から任意のアーベル群への射で判定する。
使われ方：射影の像が退化単体の生成する部分であることの普遍的特徴付け。
-/
theorem integralDegenerateProjection_annihilates_iff (X : SSet.{u}) (n : ℕ)
    (T : AddCommGrpCat.{u})
    (f : (freeAbelianSimplicialFunctor.obj X).obj (Opposite.op ⦋n⦌) ⟶ T) :
    (integralDegenerateProjection X).f n ≫ f = 0 ↔ DoldKan.DegeneraciesVanish f :=
  (DoldKan.degeneraciesVanish_iff_QInfty_f_comp f).symm

end SerrePositivity.KST.Comparison
