module
public import SerrePositivity.KST.ProExcision.CentralIdealKernelEquiv
public import SerrePositivity.KST.ProExcision.SimplicialColumnRightMultiplication

/-!
# 実 aI の標準列群と元の列群の実単体的同型

概要：単射な中心乗法による実核イデアル同型を実単体的ベクトル群に束ねる。
方針：実成分同型とその全単体射への自然性を用いる。
規約：KST Proposition 4.14 の非可換再記述。使われ方：実相対包含の因子化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単射な中心乗法による元の実列群と実 aI の列群の自然同型。
方針：各次数の実加法同型を乗法表記に移し、実係数自然性で束ねる。
規約：KST Proposition 4.14。使われ方：実アフィン相対包含の前の実ファイバー同型。 -/
def NonUnitalSimplicialRing.centralIdealColumnGroupIso (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x)) (n : ℕ) :
    I.standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat ≅
      (I.centralIdeal a ha).standardIdeal.columnGroup n ⋙ forget₂ GrpCat MonCat :=
  NatIso.ofComponents (fun k ↦
    (I.centralIdealKernelVectorAddEquiv a ha hinj n k).toMultiplicative.toMonCatIso) (by
      intro k l φ
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro v
      change (fun i ↦ I.centralIdealKernelAddEquiv a ha hinj l
          (idealCoefficientAddHom _ _ (integerUnitizationMap (I.map φ))
            (integerUnitizationMap_ideal (I.map φ)) (v.toAdd i))) =
        (fun i ↦ idealCoefficientAddHom _ _ (integerUnitizationMap ((I.centralIdeal a ha).map φ))
          (integerUnitizationMap_ideal ((I.centralIdeal a ha).map φ))
          (I.centralIdealKernelAddEquiv a ha hinj k (v.toAdd i)))
      funext i
      exact (I.centralIdealKernelAddEquiv_natural a ha hinj φ (v.toAdd i)).symm)

/-- 概要：実列群同型と実 aI 包含の合成は元の列の実右乗法。
方針：各核イデアル成分の実包含公式と標準単位化の指定元の整合を使う。
規約：KST Proposition 4.14、Lemma 4.16 の φ(v)=va。
使われ方：包含の実相対写像の実右乗法への因子化。 -/
lemma NonUnitalSimplicialRing.centralIdealColumnGroupIso_inclusion
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x)) (n : ℕ) :
    (I.centralIdealColumnGroupIso a ha hinj n).hom ≫ (I.centralIdealInclusion a ha).columnGroupMap n =
      I.standardIdeal.columnRightMap (I.standardElement a) n := by
  apply NatTrans.ext
  funext k
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro v
  change (fun i ↦ idealCoefficientAddHom _ _
      (integerUnitizationMap ((I.centralIdealInclusion a ha).app k))
      (integerUnitizationMap_ideal ((I.centralIdealInclusion a ha).app k))
      (I.centralIdealKernelAddEquiv a ha hinj k (v.toAdd i))) =
    (fun i ↦ idealRightMultiplication (I.standardIdeal.ideal k)
      (I.standardIdeal.vertexElement (I.standardElement a) k).val (v.toAdd i))
  funext i
  apply Subtype.ext
  change integerUnitizationMap ((I.centralIdealInclusion a ha).app k)
      (I.centralIdealKernelAddEquiv a ha hinj k (v.toAdd i)) =
    (v.toAdd i).val * (I.standardIdeal.vertexElement (I.standardElement a) k).val
  rw [I.standardVertexElement_coe]
  exact I.centralIdealKernelAddEquiv_inclusion a ha hinj k (v.toAdd i)

end SerrePositivity.KST.ProExcision
