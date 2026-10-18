module

public import SerrePositivity.KST.DerivedGeometry.LeftExactLowestHomology

/-!
概要：左完全関手は境界が零の次数の準同型性を保存する。
方針：核の比較の自然性と、サイクルからコホモロジーへの同型を使う。
規約：一般の準同型保存は主張しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の単一対象上の右導来比較写像。
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
概要：境界が零の短複体のコホモロジー同型は左完全関手で保たれる。
方針：サイクルの比較の自然性を使い、サイクルとコホモロジーを同一視する。
規約：両方の短複体の最初の微分が零。
使われ方：TT §3、Toën §3.2 の最下次数の準同型性。
-/
lemma leftExact_shortComplex_homologyMap_isIso {S T : ShortComplex C} (f : S ⟶ T)
    (hS : S.f = 0) (hT : T.f = 0) [IsIso (ShortComplex.homologyMap f)] :
    IsIso (ShortComplex.homologyMap (F.mapShortComplex.map f)) := by
  have : IsIso S.homologyπ := S.isIso_homologyπ hS
  have : IsIso T.homologyπ := T.isIso_homologyπ hT
  have : IsIso (ShortComplex.cyclesMap f ≫ T.homologyπ) := by
    rw [← ShortComplex.homologyπ_naturality f]
    infer_instance
  have : IsIso (ShortComplex.cyclesMap f) := IsIso.of_isIso_comp_right _ T.homologyπ
  have : IsIso (ShortComplex.cyclesMap (F.mapShortComplex.map f) ≫
      (leftExactCyclesIso F T).hom) := by
    rw [leftExactCyclesIso_naturality F f]
    infer_instance
  have : IsIso (ShortComplex.cyclesMap (F.mapShortComplex.map f)) :=
    IsIso.of_isIso_comp_right _ (leftExactCyclesIso F T).hom
  have : IsIso (F.mapShortComplex.obj S).homologyπ := (S.map F).isIso_homologyπ (by
    change F.map S.f = 0
    rw [hS, F.map_zero])
  have : IsIso (F.mapShortComplex.obj T).homologyπ := (T.map F).isIso_homologyπ (by
    change F.map T.f = 0
    rw [hT, F.map_zero])
  have : IsIso ((F.mapShortComplex.obj S).homologyπ ≫ ShortComplex.homologyMap (F.mapShortComplex.map f)) := by
    rw [ShortComplex.homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.mapShortComplex.obj S).homologyπ _

/--
概要：零未満が零の複体間の零次数準同型性は左完全関手で保たれる。
方針：対応する短複体の境界が零であることを適用する。
規約：コホモロジー零次数だけの結論。
使われ方：TT §3・§8、Toën §3.2 の injective 分解の増大の零次数比較。
-/
lemma leftExact_map_quasiIsoAt_zero {K L : CochainComplex C ℤ}
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (f : K ⟶ L) [QuasiIsoAt f 0] :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map f) 0 := by
  have hhom : IsIso (HomologicalComplex.homologyMap f 0) :=
    (quasiIsoAt_iff_isIso_homologyMap f 0).mp inferInstance
  have : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor C (.up ℤ) 0).map f)) := hhom
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact leftExact_shortComplex_homologyMap_isIso F
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) 0).map f)
    (by
      exact (K.isZero_of_isStrictlyGE 0 ((ComplexShape.up ℤ).prev 0)
        (by rw [show (ComplexShape.up ℤ).prev 0 = -1 by simp]; omega)).eq_of_src _ _)
    (by
      exact (L.isZero_of_isStrictlyGE 0 ((ComplexShape.up ℤ).prev 0)
        (by rw [show (ComplexShape.up ℤ).prev 0 = -1 by simp]; omega)).eq_of_src _ _)

end SerrePositivity.KST.DerivedGeometry
