module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinConeBoundary

/-!
概要：終域を最後の面から広げた mapping cylinder と元の mapping cylinder の右錐の比較。
方針：円柱部分を元の因子へ、終域部分を標準単体の右錐へ送り、pushout で貼る。
規約：相対 join の右錐の同型との厳密な可換性を証明する。
使われ方：Kerodon Proposition 5.2.4.5、終域の次元を下げる帰納段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終域の底の変更は relative join への prism と可換。
方針：pullback の二射影で joinMap と区間の係数の合成を計算する。
規約：単体集合と終域の射は任意。
使われ方：Kerodon Proposition 5.2.4.5、mapping cylinder の円柱部分の比較。 -/
lemma relativeJoinBaseMap_prism {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinPrism f ≫ relativeJoinBaseMap f h = relativeJoinPrism (f ≫ h) := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinBaseMap_fst, ← Category.assoc,
      relativeJoinPrism, pullback.lift_fst, Category.assoc, ← joinMap_comp,
      Category.id_comp, relativeJoinPrism, pullback.lift_fst]
  · rw [Category.assoc, relativeJoinBaseMap_snd, ← Category.assoc,
      relativeJoinPrism, pullback.lift_snd, relativeJoinPrism,
      pullback.lift_snd, whiskerLeft_comp]

/-- 概要：最後の面の包含を右錐の逆同型に合成すると元の因子の包含。
方針：右錐の順同型の左包含の式を逆同型で打ち消す。
規約：標準 n 単体の右錐。
使われ方：Kerodon Proposition 5.2.4.5、円柱と終域の貼り合わせ条件。 -/
lemma relativeJoinCylinderCone_face_inv (n : ℕ) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ (joinStdSimplexIso.{u} n 0).inv =
      joinInl (Δ[n] : SSet.{u}) Δ[0] := by
  rw [← relativeJoinCone_stdSimplex_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：大きい終域の mapping cylinder から元の mapping cylinder の右錐への比較。
方針：円柱を元の因子へ送り、終域を標準単体の右錐として右包含から写す。
規約：比較射の同値性はここでは仮定しない。
使われ方：Kerodon Proposition 5.2.4.5、右錐を経由する比較の因子化。 -/
noncomputable def relativeJoinCylinderConeMap {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ⟶
      join (pushout (prismEndpoint 1 Δ[m]) f) Δ[0] :=
  pushout.desc
    (pushout.inl (prismEndpoint 1 Δ[m]) f ≫ joinInl _ Δ[0])
    ((joinStdSimplexIso n 0).inv ≫
      joinMap (pushout.inr (prismEndpoint 1 Δ[m]) f) (𝟙 Δ[0])) (by
        rw [← Category.assoc, pushout.condition, Category.assoc,
          Category.assoc, ← Category.assoc (stdSimplex.δ (Fin.last (n + 1))),
          relativeJoinCylinderCone_face_inv, joinInl_joinMap])

/-- 概要：円柱部分で右錐への比較は元の mapping cylinder と右錐の左包含の合成。
方針：pushout の左包含の計算則を使う。
規約：始域は Δ[1]×Δ[m]。
使われ方：Kerodon Proposition 5.2.4.5、円柱上の可換性。 -/
lemma relativeJoinCylinderConeMap_inl {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout.inl (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ≫
      relativeJoinCylinderConeMap f =
        pushout.inl (prismEndpoint 1 Δ[m]) f ≫ joinInl _ Δ[0] :=
  pushout.inl_desc _ _ _

/-- 概要：終域部分で右錐への比較は右因子の右錐の包含。
方針：pushout の右包含の計算則を使う。
規約：大きい標準単体を元の終域の右錐と同定する。
使われ方：Kerodon Proposition 5.2.4.5、終域上の可換性。 -/
lemma relativeJoinCylinderConeMap_inr {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    pushout.inr (prismEndpoint 1 Δ[m]) (f ≫ stdSimplex.δ (Fin.last (n + 1))) ≫
      relativeJoinCylinderConeMap f =
        (joinStdSimplexIso n 0).inv ≫
          joinMap (pushout.inr (prismEndpoint 1 Δ[m]) f) (𝟙 Δ[0]) :=
  pushout.inr_desc _ _ _

/-- 概要：mapping cylinder の比較は右錐の比較を経由して因子化する。
方針：pushout の両因子で prism の底の変更と右因子の右錐の式を使う。
規約：相対 join の右錐の同型は標準比較射として使う。
使われ方：Kerodon Proposition 5.2.4.5、帰納仮定を join で延長する段階。 -/
lemma relativeJoinCylinderConeMap_comparison {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n]) :
    relativeJoinCylinderConeMap f ≫
      joinMap (relativeJoinCylinderComparison f) (𝟙 Δ[0]) ≫ relativeJoinConeMap f =
        relativeJoinCylinderComparison (f ≫ stdSimplex.δ (Fin.last (n + 1))) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderConeMap_inl]
    simp only [Category.assoc, reassoc_of% joinInl_joinMap]
    rw [relativeJoinConeMap_inl f,
      ← Category.assoc, relativeJoinCylinderComparison_inl,
      relativeJoinBaseMap_prism, relativeJoinCylinderComparison_inl]
  · rw [← Category.assoc, relativeJoinCylinderConeMap_inr]
    simp only [Category.assoc]
    rw [← Category.assoc (joinMap (pushout.inr (prismEndpoint 1 Δ[m]) f) (𝟙 Δ[0])),
      ← joinMap_comp, relativeJoinCylinderComparison_inr, Category.id_comp,
      relativeJoinConeMap_right, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp, relativeJoinCylinderComparison_inr]

end SerrePositivity.InfinityCategories
