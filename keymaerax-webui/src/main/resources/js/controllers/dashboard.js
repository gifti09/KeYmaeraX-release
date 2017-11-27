angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', ['$scope', function($scope) {
  $scope.cancel = function() {
      alert("KeYmaera X is shut down. Please close the window and restart the server to continue using KeYmaera X.")
      $window.close();
  }
}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', ['$scope', function($scope) {

}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl.ExtractDB', ['$scope', '$uibModalInstance', 'path', function($scope, $uibModalInstance, path) {
    $scope.extractedDatabaseLocation = path;
    $scope.close = function() {
        $uibModalInstance.dismiss('cancel');
    }
}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl', ['$scope', '$uibModal', '$http', 'sessionService', function ($scope, $uibModal, $http, sessionService) {
  $scope.intro = {
    introOptions: {},
    firstTime: false
  }

  $scope.showOverlayHelp = function() {
    $('body').chardinJs('start');
  }

  // Set the view for menu active class
  $scope.$on('routeLoaded', function (event, args) {
    $scope.theview = args.theview;
  });

  $scope.toolConfig = {};
  $http.get("/config/toolStatus").then(function(response) {
    $scope.toolConfig = response.data;
  });

  $scope.isLocal = false;
  $http.get('/isLocal')
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not determine if the KeYmaera X server is running locally")
          $scope.isLocal = data.success;
      });

  $scope.shutdown = function() {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/shutdown_dialog.html',
        controller: 'DashboardCtrl.ShutdownDialog',
        backdrop: 'static',
        size: 'sm'
      });

      $http.get("/shutdown");
  };

  $scope.logoff = function() {
      $http.get("/user/logoff");
      document.location.href = "/index_bootstrap.html";
  }

  $scope.extractdb = function() {
      $http.post('/extractdb')
          .then(function(response) {
              $uibModal.open({
                  templateUrl: 'partials/extractdb.html',
                  controller: 'DashboardCtrl.ExtractDB',
                  backdrop: "static",
                  size: 'md',
                  resolve: {
                      path: function () { return response.data.path; },
                  }
              });
          })
  };

  $scope.$emit('routeLoaded', {theview: 'dashboard'});
}]);
