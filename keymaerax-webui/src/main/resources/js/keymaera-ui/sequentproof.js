angular.module('sequentproof', ['ngSanitize','sequent','formula','angularSpinners'])
  /**
   * A sequent deduction view focused on a single path through the deduction, with links to sibling goals when
   * branching occurs.
   * {{{
   *      <k4-sequentproof userId="1" proofId="35" nodeId="N1"
                           deductionRoot="..." agenda="..." read-only="false"></k4-sequentproof>
   * }}}
   * @param userId          The user ID; for interaction with the server.
   * @param proofId         The current proof; for interaction with the server.
   * @param nodeId          The node (=task); for interaction with the server.
   * @param goalId          The goal (sequent) for cross-referencing agenda items.
   * @param deductionPath   Identifies the path to the goal (as far as loaded); Array[goalId]
   * @param proofTree       The proof tree, see provingawesome.js for schema.
   * @param agenda          The agenda, see provingawesome.js for schema.
   * @param readOnly        Indicates whether or not the proof steps should allow interaction (optional).
   */
  .directive('k4Sequentproof', ['$http', '$uibModal', '$q', '$timeout', 'sequentProofData', 'spinnerService', function($http, $uibModal, $q, $timeout, sequentProofData, spinnerService) {
    /* The directive's internal control. */
    function link(scope, element, attrs) {

      //@todo move relevant functionality into sequentproofservice.js

      scope.fetchBranchRoot = function(sectionIdx) {
        var section = scope.deductionPath.sections[sectionIdx];
        var sectionEnd = section.path[section.path.length-1];
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + sectionEnd + '/branchroot').success(function(data) {
          addBranchRoot(data, scope.agenda.itemsMap[scope.nodeId], sectionIdx);
        });
      }

      scope.isProofRootVisible = function() {
        var root = scope.proofTree.nodesMap[scope.proofTree.root];
        return scope.deductionPath.sections[scope.deductionPath.sections.length - 1].path.indexOf(root.id) >= 0;
      }

      scope.showProofRoot = function() {
        var root = scope.proofTree.nodesMap[scope.proofTree.root];
        if (scope.deductionPath.sections[scope.deductionPath.sections.length - 1].path.indexOf(root.id) < 0) {
          addBranchRoot(root, scope.agenda.itemsMap[scope.nodeId], scope.deductionPath.sections.length-1);
        }
      }

      scope.fetchPathAll = function(sectionIdx) {
        var section = scope.deductionPath.sections[sectionIdx];
        var sectionEnd = section.path[section.path.length-1];
        if (sectionEnd !== scope.proofTree.root) {
          $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + sectionEnd + '/pathall').success(function(data) {
            // TODO use numParentsUntilComplete to display some information
            $.each(data.path, function(i, ptnode) { updateProof(ptnode); });
          });
        }
      }

      /**
       * Updates the specified section by adding the proof tree node. If the node has more than 1 child, a new section
       * after the specified section is started.
       * @param proofTreeNode The node to add.
       * @param sectionIdx The section where to add the proof node.
       */
      updateSection = function(proofTreeNode, agendaItem, sectionIdx) {
        // only update if node not added previously
        if (sectionIdx+1 >= agendaItem.deduction.sections.length || agendaItem.deduction.sections[sectionIdx+1].path.indexOf(proofTreeNode.id) < 0) {
          var section = agendaItem.deduction.sections[sectionIdx];
          var sectionEnd = section.path[section.path.length-1];
          if (proofTreeNode.children != null && proofTreeNode.children.length > 1) {
            if (sectionIdx+1 >= agendaItem.deduction.sections.length || agendaItem.deduction.sections[sectionIdx+1].path[0] !== null) {
              // start new section with parent, parent section is complete if parent is root
              agendaItem.deduction.sections.splice(sectionIdx+1, 0, {path: [proofTreeNode.id], isCollapsed: false, isComplete: proofTreeNode.parent === null});
            } // else: parent already has its own section, see fetchBranchRoot
            // in any case: child's section is loaded completely if it's ending in one of the children of the proof tree node
            section.isComplete = proofTreeNode.children.indexOf(sectionEnd) >= 0;
          } else {
            // parent has exactly 1 child, append parent to child's section
            if (sectionIdx === -1) {
              showClientErrorMessage($uibModal, 'Expected a unique path section ending in a child of ' + proofTreeNode.id + ', but agenda item ' + agendaItem.id +
                ' has ' + agendaItem.sections + ' as path sections');
            } else if (proofTreeNode.parent !== null) {
              section.path.push(proofTreeNode.id);
              var parentCandidate =
                (sectionIdx+1 < agendaItem.deduction.sections.length
                ? scope.proofTree.nodesMap[agendaItem.deduction.sections[sectionIdx+1].path[0]]
                : undefined);
              section.isComplete =
                parentCandidate !== undefined && parentCandidate.children != null && parentCandidate.children.indexOf(proofTreeNode.id) >= 0;
            } else {
              if (sectionIdx+1 < agendaItem.deduction.sections.length) {
                showClientErrorMessage($uibModal, 'Received proof tree root, which can only be added to last section, but ' + sectionIdx +
                  ' is not last section in ' + agendaItem.deduction.sections);
              } else {
                agendaItem.deduction.sections.splice(sectionIdx+1, 0, {path: [proofTreeNode.id], isCollapsed: false, isComplete: true});
                section.isComplete = proofTreeNode.children != null && proofTreeNode.children.indexOf(sectionEnd) >= 0;
              }
            }
          }
        }
      }

      /**
       * Adds a proof tree node and updates the agenda sections.
       */
      updateProof = function(proofTreeNode) {
        scope.proofTree.addNode(proofTreeNode);

        // append parent to the appropriate section in all relevant agenda items
        var items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); }); // JQuery flat map
        $.each(items, function(i, v) {
          var childSectionIdx = scope.agenda.childSectionIndex(v.id, proofTreeNode);
          if (childSectionIdx >= 0) {
            updateSection(proofTreeNode, v, childSectionIdx);
          }
        });
      }

      /**
       * Adds the specified proof tree node as branch root to the specified section.
       */
      addBranchRoot = function(proofTreeNode, agendaItem, sectionIdx) {
        scope.proofTree.addNode(proofTreeNode);
        updateSection(proofTreeNode, agendaItem, sectionIdx);

        // append parent to the appropriate section in all relevant agenda items
        if (proofTreeNode.children != null) {
          var items = $.map(proofTreeNode.children, function(e) { return scope.agenda.itemsByProofStep(e); });
          $.each(items, function(i, v) {
            var childSectionIdx = scope.agenda.childSectionIndex(v.id, proofTreeNode);
            updateSection(proofTreeNode, v, childSectionIdx);
          });
        }
      }

      /** Filters sibling candidates: removes this item's goal and path */
      scope.siblingsWithAgendaItem = function(candidates) {
        var item = scope.agenda.itemsMap[scope.nodeId];
        var fp = flatPath(item);
        return (candidates != null ? candidates.filter(function(e) { return fp.indexOf(e) < 0 && scope.agenda.itemsByProofStep(e).length > 0; }) : []);
      }

      /** Applies the tactic 'tacticId' without input at the formula 'formulaId' */
      scope.onApplyTactic = function(formulaId, tacticId) {
        scope.onTactic({formulaId: formulaId, tacticId: tacticId});
      }

      /** Applies the tactic 'tacticId' with input at the formula 'formulaId' */
      scope.onApplyInputTactic = function(formulaId, tacticId, input) {
        scope.onInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
      }

      scope.onApplyTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
        scope.onTwoPositionTactic({fml1Id: fml1Id, fml2Id: fml2Id, tacticId: tacticId});
      }

      scope.fetchParentRightClick = function(event) {
        event.stopPropagation();
        // emulate hoverable popover (to come in later ui-bootstrap version) with hide on blur (need to focus for blur)
        event.target.focus();
      }

      scope.proofStepRightClick = function(event) {
        event.stopPropagation();
        event.target.focus();
      }

      scope.highlightStepPosition = function(nodeId, highlight) {
        var parent = sequentProofData.proofTree.nodesMap[nodeId];
        var fstChild = sequentProofData.proofTree.nodesMap[parent.children[0]];
        var posId = fstChild.rule.pos.replace(/\./g, "\\,");
        var element = $("#seq_"+nodeId + " #fml_"+posId);
        if (highlight) {
          if (element.text().startsWith("[") || element.text().startsWith("&lt;")) element.addClass("k4-highlight-steppos-modality");
          else element.addClass("k4-highlight-steppos");
        } else element.removeClass("k4-highlight-steppos k4-highlight-steppos-modality");
      }

      flatPath = function(item) {
        var result = [];
        $.each(item.deduction.sections, function(i, v) { $.merge(result, v.path); });
        return result;
      }

      /**
       * Fetches the parent of goal 'goalId' and updates the agenda item 'nodeId' to show an extended sequent
       * (parent appended as previous proof step below deduction view).
       */
      scope.fetchSectionParent = function(section) {
        var nodeId = section.path[section.path.length - 1];
        $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + nodeId + '/parent').success(function(data) {
          updateProof(data);
        });
      }

      /** Prunes the proof tree and agenda/deduction path below the specified step ID. */
      scope.prune = function(nodeId) {
        sequentProofData.prune(scope.userId, scope.proofId, nodeId);
      }

      /* Indicates whether the section has a parent (if its last step has a parent, and the section is not complete) */
      scope.hasParent = function(section) {
        var step = section.path[section.path.length - 1];
        return sequentProofData.proofTree.nodesMap[step].parent !== null && (!section.isComplete || section.isCollapsed);
      }

      scope.deductionPath.isCollapsed = false;
    }

    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            deductionPath: '=',
            proofTree: '=',
            agenda: '=',
            readOnly: '=?',
            onTactic: '&',
            onInputTactic: '&',
            onTwoPositionTactic: '&'
        },
        link: link,
        templateUrl: 'partials/singletracksequentproof.html'
    };
  }])
  .filter('childRuleName', function () {
    return function (input, scope) {
      var children = scope.proofTree.nodesMap[input].children;
      var loaded = $.grep(children, function(e, i) { return scope.proofTree.nodeIds().indexOf(e) >= 0; });
      return loaded.length > 0 ? scope.proofTree.nodesMap[loaded[0]].rule.name : undefined;
    };
  });
