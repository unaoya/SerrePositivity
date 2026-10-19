module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialMaps
public import SerrePositivity.KST.ProExcision.NonUnitalHatGL
public import SerrePositivity.KST.ProExcision.ComponentRingSimplex

/-!
# 非単位単体環の実係数射による ĜL の実射

概要：標準整数単位化の実係数射を成分で可逆な整数核行列に制限する。
方針：成分環の実自然性で単位性を移し、整数射影の保存を用いる。
規約：KST Proposition 4.14、各次数の行列の可逆性は要求しない。
使われ方：実 aI→I の包含による一般線形モノイドの実写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {I J : NonUnitalSimplicialRing.{u}}

/-- 概要：実係数変更と成分行列の実誘導射は可換。
方針：各成分に任意の次数の実成分環写像の自然性を用いる。
規約：KST Proposition 4.14。使われ方：実 ĜL の単位条件の保存。 -/
lemma NonUnitalSimplicialRingHom.matrix_components (f : NonUnitalSimplicialRingHom I J)
    (n q : ℕ) (A : Matrix (Fin n) (Fin n) (Unitization ℤ (I.obj (op ⦋q⦌)))) :
    (componentRingMap f.unitizationMap).mapMatrix
        (Comparison.matrixToComponents I.standardIdeal.ambient n q A) =
      Comparison.matrixToComponents J.standardIdeal.ambient n q
        ((integerUnitizationMap (f.app (op ⦋q⦌))).mapMatrix A) := by
  apply Matrix.ext
  intro i j
  exact componentRingMap_simplex f.unitizationMap q (A i j)

/-- 概要：実非単位環係数変更が誘導する各次数の実 ĜL 準同型。
方針：成分での単位性を実成分環写像で移し、整数核を保存する。
規約：KST Proposition 4.14。使われ方：実単体的 ĜL 係数射の各成分。 -/
def NonUnitalSimplicialRingHom.hatGLHom (f : NonUnitalSimplicialRingHom I J) (n q : ℕ) :
    I.hatGLSubmonoid n q →* J.hatGLSubmonoid n q where
  toFun A := ⟨(integerUnitizationMap (f.app (op ⦋q⦌))).mapMatrix A.val, by
    constructor
    · have hu := A.property.1.map (componentRingMap f.unitizationMap).mapMatrix.toMonoidHom
      change IsUnit ((componentRingMap f.unitizationMap).mapMatrix
        (Comparison.matrixToComponents I.standardIdeal.ambient n q A.val)) at hu
      rw [f.matrix_components] at hu
      exact hu
    · rw [integerUnitizationMap_fst_matrix]
      exact A.property.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ A.val B.val)

/-- 概要：実非単位単体環射が誘導する実単体的 ĜL 射。
方針：実各次数準同型を、実単位化係数射の全単体自然性で束ねる。
規約：KST Proposition 4.14。使われ方：実係数イデアル包含の安定化。 -/
def NonUnitalSimplicialRingHom.hatGLMap (f : NonUnitalSimplicialRingHom I J) (n : ℕ) :
    I.hatGL n ⟶ J.hatGL n where
  app k := MonCat.ofHom (f.hatGLHom n k.unop.len)
  naturality {k l} φ := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro A
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact congrArg (fun h : I.standardIdeal.ambient.obj k ⟶ J.standardIdeal.ambient.obj l ↦
      h.hom (A.val i j)) (f.unitizationMap.naturality φ)

end SerrePositivity.KST.ProExcision
