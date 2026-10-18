import SerrePositivity.KST.SConstruction

/-!
概要：S• 構成の公開宣言の型と公理を監査する。
方針：型の検査と公理一覧を各宣言について出力する。
規約：propext・Classical.choice・Quot.sound のみ許可。
使われ方：BGT §7 に対応する保存単位の検証。
-/

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion
#check @SerrePositivity.KST.SConstruction.arCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.arCofiberCompletion
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#check @SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#check @SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#print axioms SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#check @SerrePositivity.KST.SConstruction.arCofiberSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareChain
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#check @SerrePositivity.KST.SConstruction.curry_vertex_value
#print axioms SerrePositivity.KST.SConstruction.curry_vertex_value
#check @SerrePositivity.KST.SConstruction.arCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily
#check @SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.cofiberApex
#print axioms SerrePositivity.KST.SConstruction.cofiberApex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.arCofiberInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputOrder
#check @SerrePositivity.KST.SConstruction.arCofiberInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#check @SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#check @SerrePositivity.KST.SConstruction.frameCofiberInputs
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputs
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams
#check @SerrePositivity.KST.SConstruction.cofiberProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#check @SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#check @SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#check @SerrePositivity.KST.SConstruction.cofiberSection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection
#check @SerrePositivity.KST.SConstruction.cofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection_projection
#check @SerrePositivity.KST.SConstruction.cofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberFunctor
#check @SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.firstRowNerve
#print axioms SerrePositivity.KST.SConstruction.firstRowNerve
#check @SerrePositivity.KST.SConstruction.firstRowOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowOrder
#check @SerrePositivity.KST.SConstruction.firstRowInclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowInclusion
#check @SerrePositivity.KST.SConstruction.firstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction
#check @SerrePositivity.KST.SConstruction.gappedDiagram
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram
#check @SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#check @SerrePositivity.KST.SConstruction.firstRowSimplexIso
#print axioms SerrePositivity.KST.SConstruction.firstRowSimplexIso
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData
#check @SerrePositivity.KST.SConstruction.firstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.firstRowCofiberData
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#check @SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#check @SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#print axioms SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#check @SerrePositivity.KST.SConstruction.frame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.frame_extend_boundary
#check @SerrePositivity.KST.SConstruction.firstRowFrameOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameOrder
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap
#check @SerrePositivity.KST.SConstruction.frameRowChain_positive
#print axioms SerrePositivity.KST.SConstruction.frameRowChain_positive
#check @SerrePositivity.KST.SConstruction.frameRowChainInverse
#print axioms SerrePositivity.KST.SConstruction.frameRowChainInverse
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowIso
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowIso
#check @SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#print axioms SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#check @SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#check @SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#check @SerrePositivity.KST.SConstruction.Ar
#print axioms SerrePositivity.KST.SConstruction.Ar
#check @SerrePositivity.KST.SConstruction.arObj
#print axioms SerrePositivity.KST.SConstruction.arObj
#check @SerrePositivity.KST.SConstruction.arMap
#print axioms SerrePositivity.KST.SConstruction.arMap
#check @SerrePositivity.KST.SConstruction.arMap_id
#print axioms SerrePositivity.KST.SConstruction.arMap_id
#check @SerrePositivity.KST.SConstruction.arMap_comp
#print axioms SerrePositivity.KST.SConstruction.arMap_comp
#check @SerrePositivity.KST.SConstruction.arNerve
#print axioms SerrePositivity.KST.SConstruction.arNerve
#check @SerrePositivity.KST.SConstruction.arNerveMap
#print axioms SerrePositivity.KST.SConstruction.arNerveMap
#check @SerrePositivity.KST.SConstruction.arNerveMap_id
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_id
#check @SerrePositivity.KST.SConstruction.arNerveMap_comp
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_comp
#check @SerrePositivity.KST.SConstruction.diagramSpace
#print axioms SerrePositivity.KST.SConstruction.diagramSpace
#check @SerrePositivity.KST.SConstruction.intervalStep
#print axioms SerrePositivity.KST.SConstruction.intervalStep
#check @SerrePositivity.KST.SConstruction.intervalStep_le
#print axioms SerrePositivity.KST.SConstruction.intervalStep_le
#check @SerrePositivity.KST.SConstruction.le_intervalStep
#print axioms SerrePositivity.KST.SConstruction.le_intervalStep
#check @SerrePositivity.KST.SConstruction.arSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arSquareOrder
#check @SerrePositivity.KST.SConstruction.arSquare
#print axioms SerrePositivity.KST.SConstruction.arSquare
#check @SerrePositivity.KST.SConstruction.IsGapped
#print axioms SerrePositivity.KST.SConstruction.IsGapped
#check @SerrePositivity.KST.SConstruction.arSquare_naturality
#print axioms SerrePositivity.KST.SConstruction.arSquare_naturality
#check @SerrePositivity.KST.SConstruction.IsGapped.precomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.precomp
#check @SerrePositivity.KST.SConstruction.gappedSubcomplex
#print axioms SerrePositivity.KST.SConstruction.gappedSubcomplex
#check @SerrePositivity.KST.SConstruction.sConstruction
#print axioms SerrePositivity.KST.SConstruction.sConstruction
#check @SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#check @SerrePositivity.KST.SConstruction.sMap
#print axioms SerrePositivity.KST.SConstruction.sMap
#check @SerrePositivity.KST.SConstruction.sMap_ι
#print axioms SerrePositivity.KST.SConstruction.sMap_ι
#check @SerrePositivity.KST.SConstruction.sMap_id
#print axioms SerrePositivity.KST.SConstruction.sMap_id
#check @SerrePositivity.KST.SConstruction.sMap_comp
#print axioms SerrePositivity.KST.SConstruction.sMap_comp
#check @SerrePositivity.KST.SConstruction.simplicialSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialSConstruction
#check @SerrePositivity.KST.SConstruction.frameInclusion
#print axioms SerrePositivity.KST.SConstruction.frameInclusion
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#check @SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction
#check @SerrePositivity.KST.SConstruction.frameRowRestriction
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#check @SerrePositivity.KST.SConstruction.frameRowDiagramIso
#print axioms SerrePositivity.KST.SConstruction.frameRowDiagramIso
#check @SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#check @SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#print axioms SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#check @SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#check @SerrePositivity.KST.SConstruction.pushoutDiagrams
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagrams
#check @SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#print axioms SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#check @SerrePositivity.KST.SConstruction.pushoutProjection
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#check @SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#check @SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#check @SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#check @SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#check @SerrePositivity.KST.SConstruction.zeroChoices
#print axioms SerrePositivity.KST.SConstruction.zeroChoices
#check @SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#check @SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#check @SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#check @SerrePositivity.KST.SConstruction.IsDiagonal
#print axioms SerrePositivity.KST.SConstruction.IsDiagonal
#check @SerrePositivity.KST.SConstruction.IsPositiveRow
#print axioms SerrePositivity.KST.SConstruction.IsPositiveRow
#check @SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#print axioms SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#check @SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#print axioms SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#check @SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.FrameAr
#print axioms SerrePositivity.KST.SConstruction.FrameAr
#check @SerrePositivity.KST.SConstruction.frameForgetOrder
#print axioms SerrePositivity.KST.SConstruction.frameForgetOrder
#check @SerrePositivity.KST.SConstruction.frameNerve
#print axioms SerrePositivity.KST.SConstruction.frameNerve
#check @SerrePositivity.KST.SConstruction.framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.framePositiveRow
#check @SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#check @SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection
#check @SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#check @SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#check @SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers

#check @SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge

#check @SerrePositivity.KST.SConstruction.identityCocone
#print axioms SerrePositivity.KST.SConstruction.identityCocone

#check @SerrePositivity.KST.SConstruction.identityCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.identityCocone_isColimit

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq

#check @SerrePositivity.KST.SConstruction.identityCocone_val
#print axioms SerrePositivity.KST.SConstruction.identityCocone_val

#check @SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant
#print axioms SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant

#check @SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face
#print axioms SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face

#check @SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne
#print axioms SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne

#check @SerrePositivity.KST.SConstruction.edgeTargetShape
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_inl
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_inl

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit

#check @SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fst
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fst

#check @SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_snd
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_snd

#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareOrder

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex

#check @SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input

#check @SerrePositivity.KST.SConstruction.frameInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.frameInclusion_mono

#check @SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame

#check @SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary

#check @SerrePositivity.KST.SConstruction.intervalTriple
#print axioms SerrePositivity.KST.SConstruction.intervalTriple

#check @SerrePositivity.KST.SConstruction.arCofiberRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangleOrder

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_left

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_outer

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_right

#check @SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples
#print axioms SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples

#check @SerrePositivity.KST.SConstruction.isGapped_iff_triples
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_triples

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow

#check @SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal

#check @SerrePositivity.KST.SConstruction.HasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.HasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone

#check @SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.reindexFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.reindexFunctorCocone

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex

#check @SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isGapped_const
#print axioms SerrePositivity.KST.SConstruction.isGapped_const

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero

#check @SerrePositivity.KST.SConstruction.sMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex

#check @SerrePositivity.KST.SConstruction.firstRowZero_hom_ext
#print axioms SerrePositivity.KST.SConstruction.firstRowZero_hom_ext

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_left
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_left

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_right
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_right

#check @SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints
#print axioms SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono

#check @SerrePositivity.KST.SConstruction.arTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι

#check @SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint

#check @SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber

#check @SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom
#print axioms SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext
#print axioms SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext

#check @SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift
#print axioms SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift

#check @SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne
#print axioms SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne

#check @SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection
#print axioms SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso

#check @SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasColimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasColimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroSpanData
#print axioms SerrePositivity.KST.SConstruction.zeroSpanData

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroSpan_sources
#print axioms SerrePositivity.KST.SConstruction.zeroSpan_sources

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasColimit_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.hasColimit_zeroSpan

#check @SerrePositivity.KST.SConstruction.cofiberSpan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan

#check @SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff
#print axioms SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff

#check @SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits

#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span

#check @SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.IsZeroSpanVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroSpanVertex

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap

#check @SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource

#check @SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_right

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans_ι
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans_ι

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.spanTranspose
#print axioms SerrePositivity.KST.SConstruction.spanTranspose

#check @SerrePositivity.KST.SConstruction.spanTranspose_left
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_left

#check @SerrePositivity.KST.SConstruction.spanTranspose_right
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_right

#check @SerrePositivity.KST.SConstruction.spanTranspose_comp_self
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_comp_self

#check @SerrePositivity.KST.SConstruction.spanTransposeIso
#print axioms SerrePositivity.KST.SConstruction.spanTransposeIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_isIso
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_isIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_square
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_square

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose

#check @SerrePositivity.KST.SConstruction.arVerticalRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangleOrder

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_left

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_outer

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_right

#check @SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares
#print axioms SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_originSquares
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices

#check @SerrePositivity.KST.SConstruction.intervalMaxOrder
#print axioms SerrePositivity.KST.SConstruction.intervalMaxOrder

#check @SerrePositivity.KST.SConstruction.intervalMax
#print axioms SerrePositivity.KST.SConstruction.intervalMax

#check @SerrePositivity.KST.SConstruction.intervalMax_zero
#print axioms SerrePositivity.KST.SConstruction.intervalMax_zero

#check @SerrePositivity.KST.SConstruction.intervalMax_one
#print axioms SerrePositivity.KST.SConstruction.intervalMax_one

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism

#check @SerrePositivity.KST.SConstruction.cofiberUnitCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCorner

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant

#check @SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame

#check @SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism

#check @SerrePositivity.KST.SConstruction.cofiberTopCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberTopCorner

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_one

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner

#check @SerrePositivity.KST.SConstruction.arSquare_topCorner
#print axioms SerrePositivity.KST.SConstruction.arSquare_topCorner

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one

#check @SerrePositivity.KST.SConstruction.squareVertexLine
#print axioms SerrePositivity.KST.SConstruction.squareVertexLine

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart

#check @SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget

#check @SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame

#check @SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at

#check @SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span
#print axioms SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_span

#check @SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.firstRowEquivalence
#print axioms SerrePositivity.KST.SConstruction.firstRowEquivalence

#check @SerrePositivity.KST.SConstruction.coreSConstruction
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction

#check @SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSMap
#print axioms SerrePositivity.KST.SConstruction.coreSMap

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.coreSMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map

#check @SerrePositivity.KST.SConstruction.kanCoreIso
#print axioms SerrePositivity.KST.SConstruction.kanCoreIso

#check @SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedCoreSMap
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSMap

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget

#check @SerrePositivity.KST.SConstruction.pointedSRealization
#print axioms SerrePositivity.KST.SConstruction.pointedSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization
#print axioms SerrePositivity.KST.SConstruction.kanSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.sRealizationToKan
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne

#check @SerrePositivity.KST.SConstruction.kSpace
#print axioms SerrePositivity.KST.SConstruction.kSpace

#check @SerrePositivity.KST.SConstruction.kSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpace_kanComplex

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective

#check @SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonal_connected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_connected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected

#check @SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne

#check @SerrePositivity.KST.SConstruction.isConnected_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.isConnected_of_anodyne

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective

#check @SerrePositivity.KST.SConstruction.kanSRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_isConnected

#check @SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex

#check @SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.pointedPathAt
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint

#check @SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism

#check @SerrePositivity.KST.SConstruction.exists_loopBasepointComparison
#print axioms SerrePositivity.KST.SConstruction.exists_loopBasepointComparison

#check @SerrePositivity.KST.SConstruction.kanComparison_congr_left
#print axioms SerrePositivity.KST.SConstruction.kanComparison_congr_left

#check @SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint

#check @SerrePositivity.KST.SConstruction.realizationZeroEdge
#print axioms SerrePositivity.KST.SConstruction.realizationZeroEdge

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison

#check @SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq
#print axioms SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen

#check @SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_id
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_id

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_ι

#check @SerrePositivity.KST.SConstruction.sPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_id

#check @SerrePositivity.KST.SConstruction.sPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_comp

#check @SerrePositivity.KST.SConstruction.sPostcomp_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_sMap

#check @SerrePositivity.KST.SConstruction.simplicialSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialSPostcomp

#check @SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_id

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero

#check @SerrePositivity.KST.SConstruction.preservesChosenZero_id
#print axioms SerrePositivity.KST.SConstruction.preservesChosenZero_id

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero.comp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_id

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.kanSPostcomp
#print axioms SerrePositivity.KST.SConstruction.kanSPostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_id
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_id

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_comp

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible

#check @SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.mapJoinCocone
#print axioms SerrePositivity.KST.SConstruction.mapJoinCocone

#check @SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.squareRightEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareRightEdge_mono

#check @SerrePositivity.KST.SConstruction.squareBottomEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareBottomEdge_mono

#check @SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op
#print axioms SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasLimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasLimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroCospanData
#print axioms SerrePositivity.KST.SConstruction.zeroCospanData

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroCospan_targets
#print axioms SerrePositivity.KST.SConstruction.zeroCospan_targets

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasLimit_zeroCospan
#print axioms SerrePositivity.KST.SConstruction.hasLimit_zeroCospan

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits

#check @SerrePositivity.KST.SConstruction.functor_const_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_const_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge

#check @SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate

#check @SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate

#check @SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits

#check @SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff

#check @SerrePositivity.KST.SConstruction.functor_isStable
#print axioms SerrePositivity.KST.SConstruction.functor_isStable

#check @SerrePositivity.KST.SConstruction.sConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isStable

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image
#print axioms SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image

#check @SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sMap_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate
#print axioms SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate

#check @SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.relativeInitialVertexIso
#print axioms SerrePositivity.KST.SConstruction.relativeInitialVertexIso

#check @SerrePositivity.KST.SConstruction.ihom_pre_innerFibration
#print axioms SerrePositivity.KST.SConstruction.ihom_pre_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer

#check @SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso

#check @SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary

#check @SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso

#check @SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso
#print axioms SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso

#check @SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan

#check @SerrePositivity.KST.SConstruction.IsGapped.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsGapped.of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.squareDiagram_pre
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pre

#check @SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary

#check @SerrePositivity.KST.SConstruction.pushoutInterchange
#print axioms SerrePositivity.KST.SConstruction.pushoutInterchange

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit

#check @SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting

#check @SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone

#check @SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle

#check @SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise

#check @SerrePositivity.KST.SConstruction.sMap_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sMap_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sMapZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sMapZeroTriangle

#check @SerrePositivity.KST.SConstruction.sPostcompZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sPostcompZeroTriangle

#check @SerrePositivity.KST.SConstruction.sMap_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sMap_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_id
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_id

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_ι

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sMap
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_id
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_id

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_comp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex

#check @SerrePositivity.KST.SConstruction.StableModel
#print axioms SerrePositivity.KST.SConstruction.StableModel

#check @SerrePositivity.KST.SConstruction.stableModelCategory
#print axioms SerrePositivity.KST.SConstruction.stableModelCategory

#check @SerrePositivity.KST.SConstruction.stableModelForget
#print axioms SerrePositivity.KST.SConstruction.stableModelForget

#check @SerrePositivity.KST.SConstruction.sStableModel
#print axioms SerrePositivity.KST.SConstruction.sStableModel

#check @SerrePositivity.KST.SConstruction.sEndofunctor
#print axioms SerrePositivity.KST.SConstruction.sEndofunctor

#check @SerrePositivity.KST.SConstruction.sEndofunctorMap
#print axioms SerrePositivity.KST.SConstruction.sEndofunctorMap

#check @SerrePositivity.KST.SConstruction.simplicialStableEndofunctor
#print axioms SerrePositivity.KST.SConstruction.simplicialStableEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction

#check @SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiIndexDiagonal
#print axioms SerrePositivity.KST.SConstruction.multiIndexDiagonal

#check @SerrePositivity.KST.SConstruction.multiDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.multiRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.multiRealizationFunctor

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.StableModel.mk
#print axioms SerrePositivity.KST.SConstruction.StableModel.mk

#check @SerrePositivity.KST.SConstruction.StableModel.carrier
#print axioms SerrePositivity.KST.SConstruction.StableModel.carrier

#check @SerrePositivity.KST.SConstruction.StableModel.quasicategory
#print axioms SerrePositivity.KST.SConstruction.StableModel.quasicategory

#check @SerrePositivity.KST.SConstruction.StableModel.stable
#print axioms SerrePositivity.KST.SConstruction.StableModel.stable
