module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricDetection
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricRestriction

/-!
概要：P_Σ からの filtered・幾何学的実現保存関手は sifted 余極限を保存する。
方針：同じ Yoneda 制限の左 Kan 延長と比較し、生成操作による可逆性検出を使う。
規約：標的には filtered 余極限と幾何学的実現だけを仮定する。
使われ方：P_Σ 普遍性における二種類の保存条件の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：二つの生成操作を保つ元の関手は全小 sifted 余極限を保つ。
方針：制限の左 Kan 延長から元の関手への指定比較を生成表示で可逆と示す。
規約：元の関手自身について結論し、延長の存在へ置き換えない。
使われ方：filtered・実現保存版の普遍性への接続。 -/
lemma sigma_preservesSmallSiftedColimits_of_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hDg : HasSmallGeometricRealizations D)
    (G : SigmaPresheafInfinity C ⟶ D)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hGg : PreservesSmallGeometricRealizations G) : PreservesSmallSiftedColimits G := by
  obtain ⟨L, β, hβ⟩ := sigma_exists_leftKanExtension_of_filtered_geometric hC hD hDg
    (sigmaYonedaInfinityMap C ≫ G)
  let b := SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  obtain ⟨η, hη⟩ := (F1B.kanLeftKanExtension_homUniversal
    (sigmaYonedaInfinityMap C) β hβ G).2 (𝟙 _)
  have hb : IsIso b := sigmaLeftKanExtension_unit_isIso β hβ
  have hpre : IsIso ((hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app D)).toFunctor.map η) := by
    have hh : b ≫ (hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app D)).toFunctor.map η =
        𝟙 _ := hη
    have : IsIso (b ≫
        (hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app D)).toFunctor.map η) :=
      hh ▸ inferInstance
    exact IsIso.of_isIso_comp_left b _
  have hL := sigmaLeftKanExtension_preservesSmallSiftedColimits β hβ
  have hi : IsIso η := sigmaComparison_isIso_of_filtered_geometric hC
    (preservesSmallFiltered_of_sifted hL) hG (preservesSmallGeometric_of_sifted hL) hGg η
    (fun x ↦ by
      rw [← functorHomEvaluate_precomp η (sigmaYonedaInfinityMap C) x]
      infer_instance)
  exact hL.of_functorIso (asIso η)

/-- 概要：P_Σ 上の sifted 保存は filtered 保存と幾何学的実現保存に同値。
方針：生成に沿う十分条件と二種類の形状への制限を合わせる。
規約：標的の全小 sifted 余極限を存在仮定にしない。
使われ方：保存関手全部分 ∞ 圏の二通りの記述。 -/
lemma sigma_preservesSmallSiftedColimits_iff_filtered_geometric
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
    (hDg : HasSmallGeometricRealizations D) (G : SigmaPresheafInfinity C ⟶ D) :
    PreservesSmallSiftedColimits G ↔
      PreservesSmallKappaFilteredColimits Cardinal.aleph0 G ∧
        PreservesSmallGeometricRealizations G :=
  ⟨fun h ↦ ⟨preservesSmallFiltered_of_sifted h, preservesSmallGeometric_of_sifted h⟩,
    fun h ↦ sigma_preservesSmallSiftedColimits_of_filtered_geometric hC hD hDg G h.1 h.2⟩

end SerrePositivity.InfinityCategories.F2.Presentable
