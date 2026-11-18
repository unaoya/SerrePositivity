module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeIsoConeProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NormalizedSliceRestriction

/-!
概要：制限された錐の四角形から、指定極限の頂点射の四角形を得る。
方針：元の指定終錐への射の一意性を使い、同じ辺を頂点へ射影する。
  文献対応：HTT 1.2.13、Kerodon §7.1（Tag 02H1）の固定錐の計算。
使われ方：離散前層の重みの射に沿う元の指定切断の自然性。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

private lemma arrow_comp_congr {A : Type u} [Category.{u} A]
    {x y z x' y' z' : A} {a : x ⟶ y} {b : y ⟶ z}
    {a' : x' ⟶ y'} {b' : y' ⟶ z'}
    (ha : Arrow.mk a = Arrow.mk a') (hb : Arrow.mk b = Arrow.mk b') :
    Arrow.mk (a ≫ b) = Arrow.mk (a' ≫ b') := by
  obtain ⟨hx, hy, hα⟩ := (Arrow.mk_eq_mk_iff a a').mp ha
  obtain ⟨_, hz, hβ⟩ := (Arrow.mk_eq_mk_iff b b').mp hb
  cases hx
  cases hy
  cases hz
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hα hβ
  rw [hα, hβ]

/-- 終対象を含む制限の四角形の射影を、元の射のまま合成する。 -/
private lemma terminal_projection_square
    {C D E F X : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    [Category.{u} F] [Category.{u} X]
    (L : E ⥤ C) (R : F ⥤ D) (N : D ⥤ C) (M : F ⥤ E)
    (πC : C ⥤ X) (πD : D ⥤ X) (πE : E ⥤ X) (πF : F ⥤ X)
    (hL : L ⋙ πC = πE) (hN : N ⋙ πC = πD)
    {c : C} {d : D} {e : E} {f : F} (hc : IsTerminal c)
    (r : d ⟶ R.obj f) (l : c ≅ L.obj e) (s : N.obj d ⟶ c)
    (k : M.obj f ⟶ e) (i : N.obj (R.obj f) ⟶ L.obj (M.obj f))
    (hi : Arrow.mk (πC.map i) = Arrow.mk (𝟙 (πF.obj f)))
    (hcross : πD.obj (R.obj f) = πE.obj (M.obj f)) :
    Arrow.mk (πD.map r ≫ eqToHom hcross ≫ πE.map k) = Arrow.mk (πC.map s ≫ πC.map l.hom) := by
  have hn : Arrow.mk (πC.map (N.map r)) = Arrow.mk (πD.map r) :=
    congrArg (fun G : D ⥤ X => Arrow.mk (G.map r)) hN
  have hl : Arrow.mk (πC.map (L.map k)) = Arrow.mk (πE.map k) :=
    congrArg (fun G : E ⥤ X => Arrow.mk (G.map k)) hL
  have hir : Arrow.mk (πC.map i ≫ πC.map (L.map k)) = Arrow.mk (πE.map k) := by
    have he : πF.obj f = πE.obj (M.obj f) :=
      (congrArg Arrow.right hi).symm.trans (congrArg Arrow.left hl)
    have h := arrow_comp_congr hi (show Arrow.mk (πC.map (L.map k)) =
        Arrow.mk (eqToHom he ≫ πE.map k) by simpa only [Arrow.arrow_mk_eqToHom_comp] using hl)
    simpa only [Category.id_comp, Arrow.arrow_mk_eqToHom_comp] using h
  have hh : Arrow.mk (πC.map i ≫ πC.map (L.map k)) =
      Arrow.mk (eqToHom hcross ≫ πE.map k) := by
    simpa only [Arrow.arrow_mk_eqToHom_comp] using hir
  have h := arrow_comp_congr hn hh
  have hs : N.map r ≫ i ≫ L.map k = s ≫ l.hom := by
    apply (cancel_mono l.inv).mp
    simp only [Category.assoc, l.hom_inv_id, Category.comp_id]
    exact hc.hom_ext _ _
  rw [← Functor.map_comp, ← Functor.map_comp, hs, Functor.map_comp] at h
  exact h.symm

private lemma ho_sliceRestrictAlong_projection {A B X : SSet.{u}} {p : A ⟶ X} {q : B ⟶ X}
    (f : A ⟶ B) (h : f ≫ q = p) :
    (hoFunctor.map (sliceRestrictAlong f h)).toFunctor ⋙
        (hoFunctor.map (sliceOverProjection p)).toFunctor =
      (hoFunctor.map (sliceOverProjection q)).toFunctor := by
  rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp, sliceRestrictAlong_projection]

/-- 同じ頂点に始点を揃えたスライスの射影。 -/
def normalizedSliceHom {A X : SSet.{u}} {p : A ⟶ X}
    {d e : JoinCone p} {x : X _⦋0⦌} (h : d.vertex = x)
    (k : (HomotopyCategory.mk d : hoFunctor.obj (sliceOver p)) ⟶ HomotopyCategory.mk e) :
    (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk e.vertex :=
  eqToHom (congrArg (fun z => (HomotopyCategory.mk z : hoFunctor.obj X)) h.symm) ≫
    (hoFunctor.map (sliceOverProjection p)).toFunctor.map k

set_option backward.isDefEq.respectTransparency.types true in
/-- 底上で可換な制限四角形は、同じ指定終錐の頂点で可換になる。 -/
@[cite HTT "1.2.13" (partial := special) "底上の相対同型をもつ、元の指定極限の頂点の比較。"]
lemma limitVertexIso_restrictionSquare
    {A B A' B' S X : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory A'] [Quasicategory B'] [Quasicategory X]
    (p : A ⟶ S) (q : B ⟶ S) (p' : A' ⟶ S) (q' : B' ⟶ S)
    (b : A ⟶ B) (a : A' ⟶ B') (f : A ⟶ A') (g : B ⟶ B')
    (hb : b ≫ q = p) (ha : a ≫ q' = p') (hf : f ≫ p' = p) (hg : g ≫ q' = q)
    (ef : IsQCatEquivalence f) (eg : IsQCatEquivalence g)
    (i : VertexIso
      (relativeFunctorVertex q' p (b ≫ g) (by rw [Category.assoc, hg, hb]))
      (relativeFunctorVertex q' p (f ≫ a) (by rw [Category.assoc, ha, hf])))
    (O : S ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O))
    (c' : JoinCone (p' ≫ O)) (d' : JoinCone (q' ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) (hc' : IsLimitCone c') (hd' : IsLimitCone d') :
    let hB : b ≫ (q ≫ O) = p ≫ O := by rw [← Category.assoc, hb]
    let hA : a ≫ (q' ≫ O) = p' ≫ O := by rw [← Category.assoc, ha]
    let dB := (restrictJoinCone d b).cast hB
    let dA := (restrictJoinCone d' a).cast hA
    ∀ (s : (HomotopyCategory.mk dB : hoFunctor.obj (sliceOver (p ≫ O))) ⟶ HomotopyCategory.mk c)
      (k : (HomotopyCategory.mk dA : hoFunctor.obj (sliceOver (p' ≫ O))) ⟶ HomotopyCategory.mk c'),
    let l : (HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ HomotopyCategory.mk c'.vertex :=
      (limitVertexIsoOfOverEquivalence f ef hf O c c' hc hc').hom
    let r : (HomotopyCategory.mk d.vertex : hoFunctor.obj X) ⟶ HomotopyCategory.mk d'.vertex :=
      (limitVertexIsoOfOverEquivalence g eg hg O d d' hd hd').hom
    r ≫ normalizedSliceHom
        ((JoinCone.vertex_cast _ hA).trans (restrictJoinCone_vertex d' a)) k =
      normalizedSliceHom
        ((JoinCone.vertex_cast _ hB).trans (restrictJoinCone_vertex d b)) s ≫ l := by
  intro hB hA dB dA s k
  dsimp only [normalizedSliceHom]
  let hf' : f ≫ (p' ≫ O) = p ≫ O := by rw [← Category.assoc, hf]
  let hg' : g ≫ (q' ≫ O) = q ≫ O := by rw [← Category.assoc, hg]
  let dF := (restrictJoinCone c' f).cast hf'
  let dG := (restrictJoinCone d' g).cast hg'
  have hdF : IsLimitCone dF :=
    ((isLimitCone_iff_restrict_equivalentShape f ef c').mp hc').cast _
  have hdG : IsLimitCone dG :=
    ((isLimitCone_iff_restrict_equivalentShape g eg d').mp hd').cast _
  let L := (hoFunctor.map (sliceRestrictAlong f hf')).toFunctor
  let R := (hoFunctor.map (sliceRestrictAlong g hg')).toFunctor
  let N := (hoFunctor.map (sliceRestrictAlong b hB)).toFunctor
  let M := (hoFunctor.map (sliceRestrictAlong a hA)).toFunctor
  let πC := (hoFunctor.map (sliceOverProjection (p ≫ O))).toFunctor
  let πD := (hoFunctor.map (sliceOverProjection (q ≫ O))).toFunctor
  let πE := (hoFunctor.map (sliceOverProjection (p' ≫ O))).toFunctor
  let πF := (hoFunctor.map (sliceOverProjection (q' ≫ O))).toFunctor
  have eqF : L.obj (HomotopyCategory.mk c') = HomotopyCategory.mk dF :=
    congrArg HomotopyCategory.mk (sliceRestrictAlong_cone f hf' c')
  have eqG : R.obj (HomotopyCategory.mk d') = HomotopyCategory.mk dG :=
    congrArg HomotopyCategory.mk (sliceRestrictAlong_cone g hg' d')
  have eqB : N.obj (HomotopyCategory.mk d) = HomotopyCategory.mk dB :=
    congrArg HomotopyCategory.mk (sliceRestrictAlong_cone b hB d)
  have eqA : M.obj (HomotopyCategory.mk d') = HomotopyCategory.mk dA :=
    congrArg HomotopyCategory.mk (sliceRestrictAlong_cone a hA d')
  let l := limitConeIso c dF hc hdF ≪≫ eqToIso eqF.symm
  let r := (limitConeIso d dG hd hdG).hom ≫ eqToHom eqG.symm
  let s' := eqToHom eqB ≫ s
  let k' := eqToHom eqA ≫ k
  have hx : (b ≫ g) ≫ (q' ≫ O) = p ≫ O := by rw [← Category.assoc, Category.assoc b g q', hg, hb]
  have hy : (f ≫ a) ≫ (q' ≫ O) = p ≫ O := by rw [← Category.assoc, Category.assoc f a q', ha, hf]
  let x := (restrictJoinCone d' (b ≫ g)).cast hx
  let y := (restrictJoinCone d' (f ≫ a)).cast hy
  obtain ⟨e, he⟩ := restrictJoinCone_relativeIso_projection p q' (b ≫ g) (f ≫ a)
    (by rw [Category.assoc, hg, hb]) (by rw [Category.assoc, ha, hf]) i O d'
  have eqX : N.obj (R.obj (HomotopyCategory.mk d')) = HomotopyCategory.mk x := by
    exact (congrArg (fun t => HomotopyCategory.mk (t.app (Opposite.op ⦋0⦌) d'))
      (sliceRestrictAlong_comp b g hB hg' hx)).trans
      (congrArg HomotopyCategory.mk (sliceRestrictAlong_cone (b ≫ g) hx d'))
  have eqY : L.obj (M.obj (HomotopyCategory.mk d')) = HomotopyCategory.mk y := by
    exact (congrArg (fun t => HomotopyCategory.mk (t.app (Opposite.op ⦋0⦌) d'))
      (sliceRestrictAlong_comp f a hf' hA hy)).trans
      (congrArg HomotopyCategory.mk (sliceRestrictAlong_cone (f ≫ a) hy d'))
  let j := eqToHom eqX ≫ e.hom ≫ eqToHom eqY.symm
  change Arrow.mk (πC.map e.hom) = Arrow.mk (𝟙 (πF.obj (HomotopyCategory.mk d'))) at he
  have hj : Arrow.mk (πC.map j) = Arrow.mk (𝟙 (πF.obj (HomotopyCategory.mk d'))) := by
    simpa only [j, Functor.map_comp, eqToHom_map, Arrow.arrow_mk_comp_eqToHom,
      Arrow.arrow_mk_eqToHom_comp] using he
  have hcross : πD.obj (R.obj (HomotopyCategory.mk d')) =
      πE.obj (M.obj (HomotopyCategory.mk d')) :=
    (congrArg (fun F => F.obj (HomotopyCategory.mk d'))
      (ho_sliceRestrictAlong_projection g hg')).trans
      (congrArg (fun F => F.obj (HomotopyCategory.mk d'))
        (ho_sliceRestrictAlong_projection a hA)).symm
  have h := terminal_projection_square L R N M πC πD πE πF
    (ho_sliceRestrictAlong_projection f hf') (ho_sliceRestrictAlong_projection b hB)
    hc.isTerminalHo r l s' k' j hj hcross
  have hc₀ := limitVertexIsoOfOverEquivalence_hom_restriction p p' f hf ef O c c' hc hc' hdF
  have hd₀ := limitVertexIsoOfOverEquivalence_hom_restriction q q' g hg eg O d d' hd hd' hdG
  apply Arrow.mk_injective
  rw [hc₀, hd₀]
  simp only [r, l, s', k', Iso.trans_hom, eqToIso.hom, Functor.map_comp, eqToHom_map,
    πC, πD, πE, limitVertexIso, Functor.mapIso_hom, Category.assoc,
    eqToHom_trans_assoc, Arrow.arrow_mk_eqToHom_comp] at h ⊢
  simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom] at h ⊢
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
