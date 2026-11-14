module

public import SerrePositivity.EInfinity.SimplexCuts.FaceFamilyTensors
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFaceComparison
public import SerrePositivity.EInfinity.SimplexCuts.CompositeCutCoefficient

/-!
# 同じ合成切断と平坦に読んだ二段切断の符号付き実テンソル

Berger–Fresse §2.2.6、M14 L12a の証明分割、報告 §292。
元の面の族と整数係数の厳密な一致を、同じ斉次純粋テンソルへ適用する。
実際の余代入の括弧替えの評価とは分ける。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 同じ面の合成で読む二段切断は、元の符号付き斉次テンソルと一致（BF §2.2.6）。 -/
lemma positiveComposite_signedCutTensor_heq_nested
    (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val) (x : S _⦋q⦌) :
    HEq
      ((Surjection.compositionSign u v k c.1 *
        cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
        cutTensor A S c.2 (positiveCompositeCutWord u v k c.1) x)
      (positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        tensorValue (chains A S) (m + (n + 1))
          (fun a => (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1)
          (fun a => gen A S
            (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
            (S.map (SimplexCategory.mkHom
              (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x))) :=
  faceFamily_tensor_heq A S (positiveCompositeFaceFamily u v k c)
    (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c))
    (positiveCompositeFaceFamily_eq_nested u v k c) x _ _
    (positiveCompositeCutCoefficient_eq_nested u v k c h)

end SerrePositivity.EInfinity.SimplexCuts
