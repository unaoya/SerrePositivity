module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveEnriched
public import SerrePositivity.InfinityCategories.F1.StrictDiagramScaffoldAdjunction
public import SerrePositivity.InfinityCategories.F1.LeftStrictTransportEquivalence
public import SerrePositivity.InfinityCategories.F1.StrictDiagramPostcomposition
public import SerrePositivity.InfinityCategories.F1.StrictDiagramPrecomposition

/-!
概要：係数図式から weighted nerve の strict transport への標準比較。
方針：taut scaffold を転置し、恒等射での評価を係数と fiber の標準同型に同定する。
規約：比較は図式全体の自然変換であり、各対象の同値を独立に選ばない。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve による strict な復元の単位。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：係数図式を自身の weighted nerve の strict transport へ自然に写す。
方針：taut scaffold の底上の射を scaffold の射の全単射で転置する。
規約：係数の Kan 性を要求しない自然変換。
使われ方：Kerodon §5.3.3、strict な復元比較の標準単位。 -/
noncomputable def weightedNerveTransportUnit {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) : F ⟶ leftStrictTransportDiagram (weightedNerveProjection F) :=
  (strictDiagramScaffoldHomEquiv F (weightedNerveProjection F)).symm
    ⟨tautScaffold F, tautScaffold_projection F⟩

/-- 概要：標準単位の全次数での値は undercategory の評価を taut scaffold で写したもの。
方針：scaffold の逆対応の評価式に標準の射を代入する。
規約：係数の制限と undercategory の単体をともに任意にする。
使われ方：Kerodon §5.3.4、単位のパラメーターに関する自然性の計算。 -/
lemma weightedNerveTransportUnit_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) (n m : SimplexCategoryᵒᵖ)
    (x : (F.obj c).obj n) (α : n ⟶ m) (τ : (nerve (Under c)).obj m) :
    (((weightedNerveTransportUnit F).app c).app n x).val.app m α τ =
      (tautScaffold F).app m
        ((simplicialReplacementUnderEvaluation F c).app m (τ, (F.obj c).map α x)) :=
  strictDiagramScaffoldHomEquiv_symm_app F (weightedNerveProjection F)
    ⟨tautScaffold F, tautScaffold_projection F⟩ c n m x α τ

/-- 概要：標準単位を恒等射で評価すると、係数から weighted nerve の fiber への標準射になる。
方針：fiber の包含で比較し、taut scaffold の定値係数における式を使う。
規約：単体集合の射の等式であり、同値類での一致に弱めない。
使われ方：Kerodon §5.3.3、単位の各成分の同値性を fiber の同型で検出する。 -/
lemma weightedNerveTransportUnit_evaluate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    (weightedNerveTransportUnit F).app c ≫
      leftStrictTransportEvaluate (weightedNerveProjection F) c = weightedNerveFiberMap F c := by
  apply vertexFiber_hom_ext _ (nerveVertex c)
  have he := strictDiagramScaffoldHomEquiv_symm_evaluate_ι F (weightedNerveProjection F)
    ⟨tautScaffold F, tautScaffold_projection F⟩ c
  exact he.trans (by
    rw [simplicialReplacementConstantLift_tautScaffold]
    rfl)

/-- 概要：Kan 値の係数図式から weighted nerve の strict transport への標準単位は各対象で同値。
方針：恒等射評価の同値性を消去し、係数と fiber の厳密な同型を使う。
規約：図式全体に自然な単位の各成分について述べる。
使われ方：Kerodon Corollary 5.6.0.6、strict Kan 図式の標準復元。 -/
lemma weightedNerveTransportUnit_isQCatEquivalence {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] (c : C) :
    IsQCatEquivalence (X := F.obj c)
      (Y := leftStrictTransport (weightedNerveProjection F) c)
      ((weightedNerveTransportUnit F).app c) := by
  apply (leftStrictTransportEvaluate_isQCatEquivalence (weightedNerveProjection F) c).cancel_right
  rw [weightedNerveTransportUnit_evaluate]
  exact (qCatEquivalenceOfIso (weightedNerveFiberIso F c)).isQCatEquivalence

/-- 概要：weighted nerve の豊穣作用の評価はパラメーターを制限した族の評価。
方針：作用の自然性と相対 uncurry の回収式を合成する。
規約：パラメーターの次数と評価の次数は独立。
使われ方：Kerodon §5.3.3、単位の豊穣自然性の成分計算。 -/
lemma weightedNerveMappingSpaceMap_apply {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) (n m : SimplexCategoryᵒᵖ) (α : n ⟶ m)
    (η : (strictDiagramMappingSpace F G).obj n) (s : (weightedNerve F).obj m) :
    ((weightedNerveMappingSpaceMap F G).app n η).val.app m α s =
      (weightedNerveMappingFamily F G).app m (s, (strictDiagramMappingSpace F G).map α η) := by
  have hn := congrArg
    (fun z : (relativeFunctorSpace (weightedNerveProjection G) (weightedNerveProjection F)).obj m ↦
      z.val.app m (𝟙 m) s)
    (ConcreteCategory.congr_hom ((weightedNerveMappingSpaceMap F G).naturality α) η)
  change ((weightedNerveMappingSpaceMap F G).app m
      ((strictDiagramMappingSpace F G).map α η)).val.app m (𝟙 m) s =
    ((weightedNerveMappingSpaceMap F G).app n η).val.app m (α ≫ 𝟙 m) s at hn
  have hu := congrArg
    (fun h : weightedNerve F ⊗ strictDiagramMappingSpace F G ⟶ weightedNerve G ↦
      h.app m (s, (strictDiagramMappingSpace F G).map α η))
    (weightedNerveMappingSpaceMap_uncurry F G)
  change ((weightedNerveMappingSpaceMap F G).app m
      ((strictDiagramMappingSpace F G).map α η)).val.app m (𝟙 m) s = _ at hu
  simp only [Category.comp_id] at hn
  exact hn.symm.trans hu

/-- 概要：weighted nerve の標準単位は strict な変換の全パラメーターに関して自然。
方針：under の評価を展開し、係数の変換の自然性を初区間ごとに適用する。
規約：零単体の変換だけでなく、変換空間の射そのものの等式。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の豊穣自然性。 -/
lemma weightedNerveTransportUnit_enrichedNaturality {C : Type u} [Category.{u} C]
    (F G : C ⥤ SSet.{u}) :
    strictDiagramMappingPost (weightedNerveTransportUnit G) F =
      weightedNerveMappingSpaceMap F G ≫
        leftStrictTransportMappingSpaceMap (weightedNerveProjection F) (weightedNerveProjection G) ≫
          strictDiagramMappingPre (weightedNerveTransportUnit F)
            (leftStrictTransportDiagram (weightedNerveProjection G)) := by
  apply strictDiagramMappingHom_ext
  intro c
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro η
  apply CategoryTheory.Functor.functorHom_ext
  intro k β
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro τ
  change (((weightedNerveTransportUnit G).app c).app k ((η.val c).app k β x)).val.app m α τ = _
  rw [weightedNerveTransportUnit_app]
  change _ = ((weightedNerveMappingSpaceMap F G).app n η).val.app m
    (((𝟙 n ≫ β) ≫ α) ≫ 𝟙 m)
    (((((weightedNerveTransportUnit F).app c).app k x).val.app m (α ≫ 𝟙 m) τ))
  simp only [Category.id_comp, Category.comp_id]
  rw [weightedNerveTransportUnit_app, weightedNerveMappingSpaceMap_apply]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  dsimp [weightedNerveMappingSpaceMap, weightedNerveMappingFamily, weightedNerveTensorMap,
    weightedNerveTensorDiagram, weightedNerveMap, strictDiagramMappingEvaluation,
    tautScaffold, tautScaffoldDiagram, simplicialReplacementUnderEvaluation,
    relativeFunctorCurry]
  let δ : m ⟶ d := (stdSimplex.objEquiv z ≫
    simplexPrefixInclusion i.val m.unop.len (Nat.le_of_lt_succ i.isLt)).op
  let f := (τ.obj 0).hom
  let g := (τ.map (homOfLE (Fin.zero_le i))).right
  change (G.map g).app d ((G.map f).app d
      ((G.obj c).map δ ((G.obj c).map α ((η.val c).app k β x)))) =
    (η.val (τ.obj i).right).app d (((β ≫ α) ≫ δ) ≫ 𝟙 d)
      ((F.map g).app d ((F.map f).app d ((F.obj c).map δ ((F.obj c).map α x))))
  simp only [Category.comp_id, Category.assoc]
  have hn := ConcreteCategory.congr_hom ((η.val c).naturality (α ≫ δ) β) x
  simp only [Functor.map_comp, CategoryTheory.comp_apply, Category.assoc] at hn
  rw [← hn, η.property f, η.property g]
  exact congrArg
    (fun γ : n ⟶ d ↦ (η.val (τ.obj i).right).app d γ
      ((F.map g).app d ((F.map f).app d ((F.obj c).map δ ((F.obj c).map α x)))))
    (Category.assoc β α δ)

end SerrePositivity.InfinityCategories
