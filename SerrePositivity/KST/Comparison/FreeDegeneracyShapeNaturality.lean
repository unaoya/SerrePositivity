module

public import SerrePositivity.KST.Comparison.FreeDegeneracyShapes

/-!
# 自由な退化の次数ごとの直和表示の自然性

概要：全射を添字とする直和による次数ごとの同型を自然同型にする。
方針：各標準形を代表に取り、元の射が行の単体だけに作用することを計算する。
規約：Segal 1974 Proposition 1.6 の模型比較の余連続性の補助。
使われ方：評価関手と直和の余極限保存を自由な退化へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite

/--
概要：次数ごとの直和表示は単体集合の射について自然である。
方針：全射の形を固定した各代表で直和の構造射の自然性を使う。
規約：元の射は全射の形を変更しない。
使われ方：直和表示の自然同型の構成。
-/
theorem freeDegeneracyShapeColimitIso_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (d : SimplexCategoryᵒᵖ) :
    (freeDegeneracies.map f).app d ≫ (freeDegeneracyShapeColimitIso Y d).hom =
      (freeDegeneracyShapeColimitIso X d).hom ≫
        colim.map ((freeDegeneracyShapeDiagram d).map f) := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨p, rfl⟩ := (freeDegeneraciesNormalForm X d).symm.surjective x
  change (freeDegeneracyShapeColimitIso Y d).hom
      ((fatRealizationMap (discreteRowsFunctor.map f)).app d
        (fatNormalFormRealize (discreteRowsFunctor.obj X) d p)) = _
  rw [fatNormalFormRealize_map]
  change (Types.coproductIso (fun s : FreeDegeneracyShape d => Y.obj (op s.degree))).inv
      (freeDegeneracyShapeEquiv Y d (fatDegreeNormalize _ _
        (fatNormalFormRealize _ _ (fatNormalFormMap (discreteRowsFunctor.map f) d p)))) =
    colim.map ((freeDegeneracyShapeDiagram d).map f)
      ((Types.coproductIso (fun s : FreeDegeneracyShape d => X.obj (op s.degree))).inv
        (freeDegeneracyShapeEquiv X d (fatDegreeNormalize _ _ (fatNormalFormRealize _ _ p))))
  rw [fatDegreeNormalize_realize, fatDegreeNormalize_realize]
  let s : FreeDegeneracyShape d := ⟨p.degree, p.epi, p.epi_property⟩
  change colimit.ι ((freeDegeneracyShapeDiagram d).obj Y) ⟨s⟩
      ((f.app (op p.degree)) p.simplex) =
    colim.map ((freeDegeneracyShapeDiagram d).map f)
      (colimit.ι ((freeDegeneracyShapeDiagram d).obj X) ⟨s⟩ p.simplex)
  exact (congrArg (fun t => t p.simplex)
    (colimit.ι_map ((freeDegeneracyShapeDiagram d).map f) ⟨s⟩)).symm

/--
概要：自由な退化の各次数は、全射の形ごとの評価関手の直和と自然同型。
方針：各対象の標準形の同型と自然性の計算を組み合わせる。
規約：右辺は実際の離散図式の余極限関手。
使われ方：自由な退化の余連続性。
-/
def freeDegeneracyShapeColimitNatIso (d : SimplexCategoryᵒᵖ) :
    freeDegeneracies.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj d ≅
      freeDegeneracyShapeDiagram d ⋙ colim :=
  NatIso.ofComponents (fun X => freeDegeneracyShapeColimitIso X d)
    (fun f => freeDegeneracyShapeColimitIso_naturality f d)

end SerrePositivity.KST.Comparison
