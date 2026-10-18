module

public import SerrePositivity.KST.Comparison.StableHatGL
public import SerrePositivity.KST.Comparison.MonoidComponentsAdjunction

/-!
# 安定 ĜL の成分と安定一般線形群

概要：実際の成分モノイドを安定一般線形群と乗法的に同定する。
方針：有限 rank の比較の安定化との自然性を証明し、左随伴である成分関手と余極限を交換する。
規約：KST 式 (2.3)、Lemma 2.13 の π₀ の同定。各次数の群構造は要求しない。
使われ方：安定分類空間の基本群の具体的な計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite SSet
open scoped Simplicial

/--
概要：誘導乗法を持つ実際の成分モノイドと有限一般線形群の乗法同値。
方針：既存の成分の全単射の乗法性を零単体の代表で確認する。
規約：KST 式 (2.2)。輸送した乗法でなく零単体から降ろした乗法を用いる。
使われ方：安定化の図式の成分ごとの同型。
-/
def hatGLInducedComponentsEquiv (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    SimplicialMonoid.componentsObject (hatGLMonoidObject A r) ≃*
      (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ where
  __ := hatGLComponentsEquiv A r
  map_mul' a b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    exact hatGLVertexUnit_mul A r a b

/--
概要：一般線形群を単位とのブロック和で並べた rank の順序列。
方針：行列の安定化が単元群に誘導する準同型を使う。
規約：rank 零から始める。KST 式 (2.3)。
使われ方：安定一般線形群の余極限。
-/
def generalLinearRankSequence (R : Type u) [Semiring R] : ℕ ⥤ MonCat.{u} :=
  Functor.ofSequence (fun r => MonCat.ofHom
    (X := MonCat.of (Matrix (Fin r) (Fin r) R)ˣ)
    (Y := MonCat.of (Matrix (Fin (r + 1)) (Fin (r + 1)) R)ˣ)
    (Units.map (matrixStabilization R r)))

/--
概要：有限 rank の一般線形群の安定化の余極限。
方針：モノイドの圏の実際の順序余極限を取る。
規約：KST の GL(R) の安定 rank の意味。
使われ方：安定 ĜL の成分の同定の右辺。
-/
def stableGeneralLinear (R : Type u) [Semiring R] : MonCat.{u} :=
  colimit (generalLinearRankSequence R)

/--
概要：有限 rank の成分の比較は行列の安定化と可換する。
方針：零単体の代表で単元の値を比較し、成分への行列の写像の自然性を使う。
規約：KST 式 (2.2)、(2.3) の整合。
使われ方：rank の順序列全体の自然同型。
-/
theorem hatGLInducedComponentsEquiv_stabilization (A : SimplicialObject RingCat.{u})
    (r : ℕ) :
    SimplicialMonoid.componentsFunctor.map (hatGLStabilization A r) ≫
        (hatGLInducedComponentsEquiv A (r + 1)).toMonCatIso.hom =
      (hatGLInducedComponentsEquiv A r).toMonCatIso.hom ≫
        MonCat.ofHom (Units.map (matrixStabilization (π₀ (ringSpace A)) r)) := by
  apply MonCat.hom_ext
  apply MonoidHom.ext
  intro a
  induction a using π₀.rec with | mk a => ?_
  apply Units.ext
  change (IsUnit.unit (hatGLStabilizationAt A r 0 a).property).val =
    matrixStabilization _ r (IsUnit.unit a.property).val
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  exact matrixToComponents_stabilization A r 0 a.val

/--
概要：ĜL の成分の rank 図式と一般線形群の rank 図式の自然同型。
方針：各 rank の乗法同値と隣接する rank の可換性をまとめる。
規約：全ての順序射に関する自然性を含む。
使われ方：順序余極限を取った安定成分の同定。
-/
def hatGLRankComponentsIso (A : SimplicialObject RingCat.{u}) :
    hatGLRankSequence A ⋙ SimplicialMonoid.componentsFunctor ≅
      generalLinearRankSequence (π₀ (ringSpace A)) := by
  let α : hatGLRankSequence A ⋙ SimplicialMonoid.componentsFunctor ⟶
      generalLinearRankSequence (π₀ (ringSpace A)) :=
    NatTrans.ofSequence
      (fun r => (hatGLInducedComponentsEquiv A r).toMonCatIso.hom)
      (fun r => by
        simpa only [Functor.comp_map, hatGLRankSequence, generalLinearRankSequence,
          Functor.ofSequence_map_homOfLE_succ]
          using hatGLInducedComponentsEquiv_stabilization A r)
  exact NatIso.ofComponents (fun r => (hatGLInducedComponentsEquiv A r).toMonCatIso)
    (fun f => α.naturality f)

/--
概要：安定 ĜL の成分モノイドは GL(π₀A) と同型である。
方針：左随伴である成分関手と余極限を交換し、有限 rank の比較の余極限と合成する。
規約：KST Lemma 2.13 の安定 π₀ の同定。
使われ方：分類空間の基本群の計算。
-/
def stableHatGLComponentsIso (A : SimplicialObject RingCat.{u}) :
    SimplicialMonoid.componentsObject (stableHatGL A) ≅
      stableGeneralLinear (π₀ (ringSpace A)) :=
  preservesColimitIso SimplicialMonoid.componentsFunctor (hatGLRankSequence A) ≪≫
    HasColimit.isoOfNatIso (hatGLRankComponentsIso A)

end SerrePositivity.KST.Comparison
