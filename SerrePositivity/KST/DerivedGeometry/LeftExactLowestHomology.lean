module

public import SerrePositivity.KST.DerivedGeometry.LeftExactCycles
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：左完全関手は複体の最下次数のコホモロジーを保存する。
方針：最下次数では境界が零なのでサイクルの核の保存だけを使う。
規約：他の次数のコホモロジー保存は仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の導来切断の次数零比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/--
概要：左完全関手のサイクル比較は短複体の射に自然。
方針：サイクルの包含の単射性と核の射の可換性で示す。
規約：余核保存を要求しない。
使われ方：TT §3、Toën §3.2 の最下次数の比較の自然性。
-/
lemma leftExactCyclesIso_naturality {S T : ShortComplex C} (f : S ⟶ T) :
    ShortComplex.cyclesMap (F.mapShortComplex.map f) ≫ (leftExactCyclesIso F T).hom =
      (leftExactCyclesIso F S).hom ≫ F.map (ShortComplex.cyclesMap f) := by
  apply (cancel_mono (F.map T.iCycles)).mp
  simp only [Category.assoc, leftExactCyclesIso_hom_iCycles,
    ← F.map_comp, ShortComplex.cyclesMap_i]
  rw [F.map_comp, ← Category.assoc, leftExactCyclesIso_hom_iCycles]
  exact ShortComplex.cyclesMap_i (F.mapShortComplex.map f)

/--
概要：左完全関手は境界が零の次数のコホモロジーを保存する。
方針：両辺のサイクルからコホモロジーへの射と核の比較同型を合成する。
規約：整数添字複体の下限を零とする。
使われ方：TT §3・§8、Toën §3.2 の injective 分解の次数零の計算。
-/
def leftExactHomologyZeroIso (K : CochainComplex C ℤ) [K.IsStrictlyGE 0] :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).homology 0 ≅ F.obj (K.homology 0) := by
  let L := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hK : K.d (-1) 0 = 0 := by
    exact (K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
  have hL : L.d (-1) 0 = 0 := by
    change F.map (K.d (-1) 0) = 0
    rw [hK, F.map_zero]
  exact (L.isoHomologyπ (-1) 0 (by simp) hL).symm ≪≫
    leftExactCyclesIso F (K.sc 0) ≪≫ F.mapIso (K.isoHomologyπ (-1) 0 (by simp) hK)

end SerrePositivity.KST.DerivedGeometry
