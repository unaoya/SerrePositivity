module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech

/-!
# 高次 δ 座標の Čech 余脈体の多項式表示

## 概要
高次 δ 座標の Čech 余脈体では、各頂点に独立の多項式変数を置く。

## 方針
頂点ごとの生成元によって、余脈体の普遍性と多項式環の普遍性を比較する。

## 規約
各写像は頂点の添字を移し、変数名を保つ。

## 使われ方
結晶模型の高次座標と切断付き Čech 因子の照合。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (k : Type u) [CommRing k] (r : ℕ)
local notation "K" => CommRingCat.of k
local notation "A" => Under (CommRingCat.of k)
private abbrev extraCechUnder := (extraCechArrow k r).cechConerve
local notation "E" => extraCechUnder k r

private def extraPolynomial : CosimplicialAlgebra k where
  obj n := CommRingCat.mkUnder K (extraVariables k r n.len)
  map θ := (MvPolynomial.rename (fun x : (Fin r × ℕ) × Fin (_ + 1) =>
    (x.1, θ.toOrderHom x.2))).toUnder
  map_id _ := by
    ext x
    change MvPolynomial.rename (fun a => (a.1, a.2)) x = x
    rw [show (fun a : (Fin r × ℕ) × Fin (_ + 1) => (a.1, a.2)) = id by rfl,
      MvPolynomial.rename_id]
    rfl
  map_comp θ ψ := by
    ext x
    change MvPolynomial.rename _ x = MvPolynomial.rename _ (MvPolynomial.rename _ x)
    rw [MvPolynomial.rename_rename]
    rfl

private def extraInsertion (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (extraCechArrow k r).right ⟶ (extraPolynomial k r).obj n :=
  (MvPolynomial.rename (fun x : Fin r × ℕ => (x, i))).toUnder

private def cechToPolynomialApp (n : SimplexCategory) :
    (E).obj n ⟶ (extraPolynomial k r).obj n :=
  WidePushout.desc (Under.homMk ((extraPolynomial k r).obj n).hom (Category.id_comp _))
    (extraInsertion k r n) (fun _ => baseHom_unique k _ _)

private theorem cechToPolynomialApp_ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) => (extraCechArrow k r).hom) i ≫
      cechToPolynomialApp k r n = extraInsertion k r n i :=
  WidePushout.ι_desc _ _ _ _ i

private def vertexInclusion (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (extraCechArrow k r).right ⟶ (E).obj n :=
  WidePushout.ι (fun _ : Fin (n.len + 1) => (extraCechArrow k r).hom) i

private def polyToCechRing (n : SimplexCategory) :
    extraVariables k r n.len →+* ((E).obj n).right :=
  MvPolynomial.eval₂Hom ((E).obj n).hom.hom
    (fun x => (vertexInclusion k r n x.2).right (MvPolynomial.X x.1))

private def polynomialToCechApp (n : SimplexCategory) :
    (extraPolynomial k r).obj n ⟶ (E).obj n :=
  Under.homMk (CommRingCat.ofHom (polyToCechRing k r n)) (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact MvPolynomial.eval₂Hom_C _ _ _)

private theorem extraInsertion_polyToCech (n : SimplexCategory) (i : Fin (n.len + 1)) :
    extraInsertion k r n i ≫ polynomialToCechApp k r n = vertexInclusion k r n i := by
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  let f : MvPolynomial (Fin r × ℕ) k →+* ((E).obj n).right :=
    (vertexInclusion k r n i).right.hom
  change (polyToCechRing k r n).comp (MvPolynomial.rename (fun x : Fin r × ℕ => (x,i))).toRingHom = f
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change polyToCechRing k r n (MvPolynomial.rename (fun x : Fin r × ℕ => (x,i))
      (MvPolynomial.C a)) = f (MvPolynomial.C a)
    rw [MvPolynomial.rename_C, polyToCechRing, MvPolynomial.eval₂Hom_C]
    exact (ConcreteCategory.congr_hom (vertexInclusion k r n i).w a).symm
  · intro j
    change polyToCechRing k r n (MvPolynomial.rename (fun x : Fin r × ℕ => (x,i))
      (MvPolynomial.X j)) = f (MvPolynomial.X j)
    rw [MvPolynomial.rename_X, polyToCechRing, MvPolynomial.eval₂Hom_X']
    rfl

private theorem polynomialToCech_cechToPolynomial (n : SimplexCategory) :
    polynomialToCechApp k r n ≫ cechToPolynomialApp k r n = 𝟙 _ := by
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  let g : ((E).obj n).right →+* extraVariables k r n.len :=
    (cechToPolynomialApp k r n).right.hom
  change g.comp (polyToCechRing k r n) = RingHom.id _
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change g (polyToCechRing k r n (MvPolynomial.C a)) = MvPolynomial.C a
    rw [polyToCechRing, MvPolynomial.eval₂Hom_C]
    exact ConcreteCategory.congr_hom (cechToPolynomialApp k r n).w a
  · rintro ⟨j,i⟩
    change g (polyToCechRing k r n (MvPolynomial.X (j,i))) = MvPolynomial.X (j,i)
    rw [polyToCechRing, MvPolynomial.eval₂Hom_X']
    exact (ConcreteCategory.congr_hom
      (congrArg Under.Hom.right (cechToPolynomialApp_ι k r n i)) (MvPolynomial.X j)).trans
        (MvPolynomial.rename_X _ _)

private theorem cechToPolynomial_polynomialToCech (n : SimplexCategory) :
    cechToPolynomialApp k r n ≫ polynomialToCechApp k r n = 𝟙 _ := by
  apply WidePushout.hom_ext
  · intro i
    change vertexInclusion k r n i ≫ cechToPolynomialApp k r n ≫ polynomialToCechApp k r n =
      vertexInclusion k r n i ≫ 𝟙 _
    erw [← Category.assoc, cechToPolynomialApp_ι, extraInsertion_polyToCech, Category.comp_id]
  · exact baseHom_unique k _ _

private def extraPolynomialIsoUnder : (E) ≅ extraPolynomial k r :=
  NatIso.ofComponents (fun n =>
    ⟨cechToPolynomialApp k r n, polynomialToCechApp k r n,
      cechToPolynomial_polynomialToCech k r n, polynomialToCech_cechToPolynomial k r n⟩)
    (fun {m n} θ => by
      apply WidePushout.hom_ext
      · intro i
        erw [← Category.assoc, Arrow.cechConerve_map, WidePushout.ι_desc,
          cechToPolynomialApp_ι, ← Category.assoc, cechToPolynomialApp_ι]
        apply Under.UnderMorphism.ext
        apply CommRingCat.hom_ext
        apply MvPolynomial.ringHom_ext'
        · apply RingHom.ext
          intro a
          change MvPolynomial.rename _ (MvPolynomial.C a) =
            MvPolynomial.rename _ (MvPolynomial.rename _ (MvPolynomial.C a))
          simp only [MvPolynomial.rename_C]
        · intro j
          change MvPolynomial.rename _ (MvPolynomial.X j) =
            MvPolynomial.rename _ (MvPolynomial.rename _ (MvPolynomial.X j))
          simp only [MvPolynomial.rename_X]
      · exact baseHom_unique k _ _)

/-- 高次 δ 座標の Čech 余脈体の台環は多項式 Čech 余脈体。 -/
def crystallineExtraCechPolynomialIso :
    extraCech k r ≅ polynomialCech k (Fin r × ℕ) :=
  Functor.isoWhiskerRight (extraPolynomialIsoUnder k r) (Under.forget K)

end SerrePositivity.BhattScholze.Prismatic
