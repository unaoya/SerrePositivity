module

public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldIntervalDiagram

/-!
概要：二点鎖上の simplicial replacement の通常の写像円柱表示。
方針：有限順序上の pushout の三つの部分を標準 1 単体と二つの係数値へ移す。
規約：これは厳密な単体集合の同型であり、全空間の同値判定は別に示す。
使われ方：Kerodon Example 5.3.2.13、Theorem 5.2.4.1、1 単体上の scaffold 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二点鎖上の simplicial replacement は係数の射の写像円柱となる pushout。
方針：末尾の一点とその係数値の同型、および nerve と標準 1 単体の同型で分解を移す。
規約：貼り合わせる端点は一であり、零端の係数値は prism の始点に残る。
使われ方：Kerodon Example 5.3.2.13、Theorem 5.2.4.1、scaffold 比較の初期帰納段階。 -/
lemma scaffoldInterval_isPushout (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    IsPushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldIntervalMap F)
      (scaffoldIntervalPrism F) (simplicialReplacementConstantLift F (ULift.up 1)) := by
  let K := F.obj (ULift.up 0)
  let j := simplicialReplacementConstantLift (scaffoldFiniteTail 0 ⋙ F) (ULift.up 0)
  have : IsIso j :=
    simplicialReplacementConstantLift_isIso (C := ULift.{u} (Fin 1)) _ _
  have : IsIso (snd (nerve (ULift.{u} (Fin 1))) K) :=
    nervePoint_snd_isIso (ULift.up (0 : Fin 1)) K
  let eA := asIso (snd (nerve (ULift.{u} (Fin 1))) K)
  let eB := (tensorRight K).mapIso (stdSimplex.isoNerve.{u} 1).symm
  let eC := (asIso j).symm
  apply (scaffoldFiniteReplacement_isPushout 0 F).flip.of_iso eA eB eC (Iso.refl _)
  · exact scaffoldIntervalTail_endpoint K
  · change _ ≫ inv j = snd (nerve (ULift.{u} (Fin 1))) K ≫ scaffoldIntervalMap F
    rw [scaffoldIntervalTail_assembly]
    change (snd (nerve (ULift.{u} (Fin 1))) K ≫ scaffoldIntervalMap F ≫ j) ≫ inv j = _
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · change _ ≫ 𝟙 _ =
      (stdSimplex.isoNerve.{u} 1).inv ▷ K ≫
        ((stdSimplex.isoNerve.{u} 1).hom ▷ K ≫ _)
    rw [Category.comp_id, ← Category.assoc, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  · change simplicialReplacementBaseMap (scaffoldFiniteTail 0) F ≫ 𝟙 _ =
      inv j ≫ simplicialReplacementConstantLift F (ULift.up 1)
    rw [Category.comp_id]
    apply (cancel_epi j).1
    rw [IsIso.hom_inv_id_assoc]
    exact scaffoldIntervalTail_constantLift F

/-- 概要：二点鎖上の simplicial replacement と係数の射の写像円柱の明示的な同型。
方針：標準の写像円柱の pushout と、構成した全空間の pushout の一意性を使う。
規約：円柱は標準 1 単体と F(0) の直積、終域部分は F(1)。
使われ方：Kerodon Example 5.3.2.13、写像円柱の普遍性からの scaffold の構成。 -/
noncomputable def simplicialReplacementIntervalIso (F : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    simplicialReplacement F ≅
      pushout (prismEndpoint 1 (F.obj (ULift.up 0))) (scaffoldIntervalMap F) :=
  (scaffoldInterval_isPushout F).isoPushout

end SerrePositivity.InfinityCategories
