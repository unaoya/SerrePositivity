module

public import SerrePositivity.KST.Descent.FiniteZariskiCover

/-!
# 有限非交和の各成分による実際の Zariski 被覆

## 概要
有限型の圏の標準有限非交和を、その指定包含による有限 Zariski 被覆として構成する。

## 方針
underlying scheme が標準非交和である既存の明示的な構成から、余極限の指定同型で移す。

## 規約
包含の指定射を変えずに開埋め込みと全基礎点の持ち上げを供給する。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の有限非交和保存の導出。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {ι : Type u} [Finite ι]
  (X : ι → FiniteTypeSchemes S)

/-- 概要：明示的な有限型非交和と選択された標準非交和の指定同型（公理 (1)）。
方針：同じ指定成分の余極限の一意性を使う。
規約：元の基底上の同型。使われ方：スキームの開被覆から標準非交和へ移す。 -/
def finiteTypeCoproductComparisonIso : finiteTypeCoproduct X ≅ ∐ X :=
  (finiteTypeCoproductIsColimit X).coconePointUniqueUpToIso (coproductIsCoproduct X)

/-- 概要：指定同型は元の成分の包含を標準包含に送る（公理 (1)）。
方針：余極限比較の指定包含の合成式。
規約：射の厳密な等式。使われ方：開埋め込みと点の持ち上げの移送。 -/
theorem finiteTypeCoproductComparisonIso_inclusion (i : ι) :
    finiteTypeCoproductInclusion X i ≫ (finiteTypeCoproductComparisonIso X).hom = Sigma.ι X i :=
  (finiteTypeCoproductIsColimit X).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct X) ⟨i⟩

/-- 概要：元の有限型の圏の標準非交和の各包含は開埋め込み（公理 (1)）。
方針：スキームの標準非交和の包含と余極限比較の同型の合成に書く。
規約：標準包含そのものの性質。使われ方：成分による有限 Zariski 被覆。 -/
instance finiteTypeCoproduct_isOpenImmersion_inclusion (i : ι) :
    IsOpenImmersion (Sigma.ι X i).hom.left := by
  have : IsIso (finiteTypeCoproductComparisonIso X).hom.hom.left :=
    (finiteTypeSchemesForget S).map_isIso (finiteTypeCoproductComparisonIso X).hom
  have hi : IsOpenImmersion (Sigma.ι (fun i ↦ (X i).obj.left) i) :=
    (sigmaOpenCover (fun i ↦ (X i).obj.left)).map_prop i
  have he : IsOpenImmersion (finiteTypeCoproductComparisonIso X).hom.hom.left := inferInstance
  rw [← finiteTypeCoproductComparisonIso_inclusion X i]
  change IsOpenImmersion
    ((Sigma.ι (fun i ↦ (X i).obj.left) i) ≫ (finiteTypeCoproductComparisonIso X).hom.hom.left)
  exact @IsOpenImmersion.comp _ _ _ _ _ hi he

/-- 概要：標準有限非交和の指定包含による実際の有限 Zariski 被覆（公理 (1)）。
方針：スキームの標準非交和の開被覆の持ち上げを、指定余極限同型で移す。
規約：空の成分族も含む。使われ方：公理 (1) の元の比較への適用。 -/
def finiteCoproductZariskiCover : FiniteTypeZariskiCover (∐ X) where
  Index := ι
  finite := inferInstance
  obj := X
  inclusion i := Sigma.ι X i
  openImmersion i := inferInstance
  covers y := by
    let e := finiteTypeCoproductComparisonIso X
    let y₀ := e.inv.hom.left y
    let cov := sigmaOpenCover (fun i ↦ (X i).obj.left)
    obtain ⟨x, hx⟩ := cov.covers y₀
    refine ⟨cov.idx y₀, x, ?_⟩
    have h := finiteTypeCoproductComparisonIso_inclusion X (cov.idx y₀)
    calc
      (Sigma.ι X (cov.idx y₀)).hom.left x =
          e.hom.hom.left ((Sigma.ι (fun i ↦ (X i).obj.left) (cov.idx y₀)) x) := by
        exact (congrArg (fun f ↦ f.hom.left x) h).symm
      _ = e.hom.hom.left y₀ := congrArg (fun t ↦ e.hom.hom.left t) hx
      _ = y := congrArg (fun f ↦ f.hom.left y) e.inv_hom_id

end SerrePositivity.KST.Descent
