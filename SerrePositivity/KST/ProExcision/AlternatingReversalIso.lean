module
public import SerrePositivity.KST.ProExcision.AlternatingReversalSign

/-!
# 単体の順序反転の自然な交代鎖同型

概要：順序を反転した単体的加群の交代面写像複体を元の複体と自然な実同型で結ぶ。
方針：各次数の符号と反転境界の公式を使う。
規約：KST Proposition 4.14、SW92 §1.2 の反対 bar の比較。実現の未証明な同定を使わない。
使われ方：非可換な列側から行側へのホモロジー比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
open AlgebraicTopology

/-- 概要：順序反転の各次数の符号付き実同型。
方針：同じ符号を逆にも掛け、符号の二乗が 1 であることを使う。
規約：SW92 §1.2 の実鎖比較。使われ方：反転の実鎖同型の成分。 -/
def reversalChainComponentIso (X : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) :
    (AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X)).X n ≅
      (AlternatingFaceMapComplex.obj X).X n where
  hom := reversalChainSign n • (SimplicialObject.opObjIso (X := X) (n := op ⦋n⦌)).hom
  inv := reversalChainSign n • (SimplicialObject.opObjIso (X := X) (n := op ⦋n⦌)).inv
  hom_inv_id := by
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Iso.hom_inv_id,
      smul_smul, reversalChainSign_mul_self, one_smul]
  inv_hom_id := by
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Iso.inv_hom_id,
      smul_smul, reversalChainSign_mul_self, one_smul]

/-- 概要：順序反転の符号付き実鎖写像。
方針：次の次数の符号の漸化式と反転境界の公式を使う。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：行側比較に必要な実鎖同型の正方向。 -/
def alternatingReversalMap (X : SimplicialObject (ModuleCat.{u} ℤ)) :
    AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X) ⟶
      AlternatingFaceMapComplex.obj X :=
  ChainComplex.ofHom (fun n ↦ (reversalChainComponentIso X n).hom) (fun n ↦ by
    simp only [AlternatingFaceMapComplex.obj, ChainComplex.of_d]
    change (reversalChainSign (n + 1) • (SimplicialObject.opObjIso (X := X) (n := op ⦋n + 1⦌)).hom) ≫
        AlternatingFaceMapComplex.objD X n =
      AlternatingFaceMapComplex.objD (SimplicialObject.opFunctor.obj X) n ≫
        (reversalChainSign n • (SimplicialObject.opObjIso (X := X) (n := op ⦋n⦌)).hom)
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      alternatingReversalDifferential, smul_smul]
    change ((-1 : ℤ) ^ (n + 1) * reversalChainSign n) • _ =
      (reversalChainSign n * (-1 : ℤ) ^ (n + 1)) • _
    rw [mul_comm])

/-- 概要：順序反転の自然な符号付き実鎖同型。
方針：構成済みの実鎖写像と各成分の実同型を束ねる。
規約：KST Proposition 4.14、SW92 §1.2。実現やホモロジーの反転不変性を仮定しない。
使われ方：反対モノイドの bar のホモロジーの移送。 -/
def alternatingReversalIso (X : SimplicialObject (ModuleCat.{u} ℤ)) :
    AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X) ≅
      AlternatingFaceMapComplex.obj X :=
  HomologicalComplex.Hom.isoOfComponents (reversalChainComponentIso X)
    (fun i j _ ↦ (alternatingReversalMap X).comm i j)

/-- 概要：実反転鎖同型は単体的加群の実射に自然。
方針：反転の次数ごとの同型の自然性と整数倍の合成則を使う。
規約：SW92 §1.2、相対項を移すための自然性。
使われ方：相対写像の零化の反対 bar への移送。 -/
lemma alternatingReversalIso_natural {X Y : SimplicialObject (ModuleCat.{u} ℤ)} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map (SimplicialObject.opFunctor.map f) ≫ (alternatingReversalIso Y).hom =
      (alternatingReversalIso X).hom ≫ AlternatingFaceMapComplex.map f := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SimplicialObject.opFunctor.map f).app (op ⦋n⦌) ≫
      (reversalChainSign n • (SimplicialObject.opObjIso (X := Y) (n := op ⦋n⦌)).hom) =
    (reversalChainSign n • (SimplicialObject.opObjIso (X := X) (n := op ⦋n⦌)).hom) ≫ f.app (op ⦋n⦌)
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1

end SerrePositivity.KST.ProExcision
