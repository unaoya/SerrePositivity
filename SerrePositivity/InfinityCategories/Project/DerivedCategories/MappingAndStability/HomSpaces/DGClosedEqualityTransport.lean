module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierDenominators

/-! # 元の閉射の対象等式による輸送と実辺の保存

概要：元の閉対象間の等式輸送射を合成しても、元の実一次単体は厳密に同じになる。
方針：対象等式を消去して恒等合成へ戻し、実分母条件を同じ辺の等式で運ぶ。
規約：H⁰ だけの比較に弱めない。使われ方：各回収始域への同じ追加閉分母の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 終対象の元の等式輸送射を後合成した、同じ閉射。 -/
def dgClosedTargetTransport {x y z : D}
    (g : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (h : y = z) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z :=
  g ≫ eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)) h)

/-- 終対象を等式で輸送しても、指定された元の実辺は厳密に同じ。 -/
lemma dgClosedTargetTransport_edge {x y z : D}
    (g : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (h : y = z) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgClosedTargetTransport A D g h)).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge := by
  cases h
  simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id]

/-- 同じ実辺を保つ終対象等式輸送は、元の実 Verdier 分母条件をそのまま保つ。 -/
lemma dgClosedTargetTransport_mem (P : Set D) {x y z : D}
    (g : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (h : y = z)
    (hg : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D g).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (dgClosedTargetTransport A D g h)).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P :=
  (congrArg (fun e => e ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) (dgClosedTargetTransport_edge A D g h)).mpr hg

/-- 終対象の等式輸送は、指定した閉前合成と厳密に可換。 -/
lemma dgClosedTargetTransport_comp {w x y z : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) w ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (g : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) (h : y = z) :
    dgClosedTargetTransport A D (r ≫ g) h = r ≫ dgClosedTargetTransport A D g h :=
  Category.assoc r g _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
